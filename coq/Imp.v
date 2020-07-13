Require Import Coq.Strings.String.
Require Import Coq.Unicode.Utf8.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq
  ssrint rat ssralg ssrnum bigop.

From extructures Require Import ord fset fmap ffun.

From void Require Import void.

From deriving Require Import deriving.

From RandC Require Import Extra Expr Prob.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.
Local Open Scope prob_scope.

Local Notation assignment := {fmap var -> {prob zexpr}}.
Local Notation subst := (ffun (fun v : var => ZSym v)).
Local Notation state := (ffun (fun x : var => 0 : int)).

Inductive com :=
| CSkip
| CAssn of assignment & com
| CIf of bexpr & com & com & com
| CBlock of {fset var} & com & com.

Definition com_indMixin := [indMixin for com_rect].
Canonical com_indType := IndType _ com com_indMixin.
Definition com_eqMixin := [derive eqMixin for com].
Canonical com_eqType := EqType com com_eqMixin.

Implicit Types (c : com) (assn : assignment) (σ : subst)
  (st : state) (defs : formulas) (vs locals : {fset var}) (v : var).

Definition app_subst σ s :=
  if s is SVar v then σ v else ZSym s.

Definition subst_comp σ1 σ2 : subst :=
  mkffun (fun v => subst_zexpr (app_subst σ1) (σ2 v))
         (supp σ1 :|: supp σ2).

Lemma subst_compE σ1 σ2 v :
  subst_comp σ1 σ2 v =
  subst_zexpr (app_subst σ1) (σ2 v).
Proof.
rewrite /subst_comp mkffunE in_fsetU !mem_supp.
case: eqP=> //= ev1; case: eqP=> //= ev2.
by rewrite ev2 /= ev1.
Qed.

Definition subst_assn σ assn : assignment :=
  mapm (fun pe => sample: e <- pe;
                  dirac (subst_zexpr (app_subst σ) e))
       assn.

Lemma subst_assnE σ assn v :
  subst_assn σ assn v =
  omap (fun pe => sample: e <- pe; dirac (subst_zexpr (app_subst σ) e))
       (assn v).
Proof. by rewrite /subst_assn mapmE. Qed.

Definition assn_vars defs assn :=
  \bigcup_(pe <- codomm assn)
    \bigcup_(e <- supp pe) zexpr_vars defs e.

Definition subst_vars defs σ :=
  \bigcup_(v <- supp σ) zexpr_vars defs (σ v).

Definition Assn assn :=
  if assn == emptym then CSkip
  else CAssn assn CSkip.

Definition DAssn σ := Assn (mapm dirac (val σ)).

Definition Block vs c :=
  if vs == fset0 then c
  else if c == CSkip then CSkip
  else CBlock vs c CSkip.

Fixpoint Seq c1 c2 :=
  match c1 with
  | CSkip => c2
  | CAssn assn c1 => CAssn assn (Seq c1 c2)
  | CIf e cthen celse c1 => CIf e cthen celse (Seq c1 c2)
  | CBlock vs c c1 => CBlock vs c (Seq c1 c2)
  end.

Infix ";;" := Seq (at level 40, left associativity).

Lemma SeqA : associative Seq.
Proof.
move=> c1 c2 c3.
elim: c1=> [|assn c1 IH|b cthen _ celse _ c1 IH|vs block _ c1 IH] /=;
congruence.
Qed.

Lemma Seqc1 c : c;; CSkip = c.
Proof. elim: c=> //= *; congruence. Qed.

Definition do_subst defs σ st :=
  updm st (mapm (feval_zexpr defs st) (val σ)).

Lemma do_subst0 defs st : do_subst defs emptyf st = st.
Proof.
by apply/eq_ffun=> v /=; rewrite /do_subst updmE mapmE /=.
Qed.

Lemma do_substE defs σ st v :
  do_subst defs σ st v = feval_zexpr defs st (σ v).
Proof.
rewrite /do_subst updmE mapmE /appf.
by case: (val σ v)=> [e|] //=.
Qed.

Definition do_assn defs assn st : {prob state} :=
  sample: expr <- mapm_p id assn;
  dirac (updm st (mapm (feval_zexpr defs st) expr)).

Lemma do_assnP defs assn st st' v :
  st' \in supp (do_assn defs assn st) ->
  if assn v is Some p then
    exists2 e, e \in supp p & st' v = feval_zexpr defs st e
  else st' v = st v.
Proof.
case/supp_sampleP=> /= vals /supp_mapm_pP [ed valsP] /supp_diracP {st'}->.
rewrite updmE mapmE.
case assn_v: (assn v)=> [p|].
  have /dommP [e vals_v]: v \in domm vals by rewrite -ed mem_domm assn_v.
  have e_p := valsP _ _ _ assn_v vals_v.
  by exists e=> //; rewrite vals_v /=.
by have /dommPn -> /=: v \notin domm vals by rewrite -ed mem_domm assn_v.
Qed.

Lemma do_assn0 defs st : do_assn defs emptym st = dirac st.
Proof.
rewrite /do_assn mapm_p0 sample_diracL; congr dirac.
by apply/eq_ffun=> v; rewrite updmE mapmE.
Qed.

Lemma do_assnD defs σ st :
  do_assn defs (mapm dirac (val σ)) st = dirac (do_subst defs σ st).
Proof.
rewrite /do_assn mapm_p_comp.
under eq_mapm_p=> e do rewrite /=.
by rewrite mapm_p_dirac sample_diracL.
Qed.

Definition do_block vs block st : {prob state} :=
  let new := updm st (mkfmapf (fun=> 0%R) vs) in
  sample: st' <- block new;
  dirac (updm st' (mkfmapf st vs)).

Lemma do_blockE (T : ordType) vs (block : state -> {prob state}) st (cont : state -> {prob T}) :
  sample (do_block vs block st) cont =
  (let new := updm st (mkfmapf (fun=> 0%R) vs) in
   sample: st' <- block new;
   cont (updm st' (mkfmapf st vs))).
Proof.
rewrite /= /do_block !sampleA.
by under eq_sample do rewrite sample_diracL.
Qed.

Fixpoint run defs c st {struct c} : {prob state} :=
  match c with
  | CSkip =>
    dirac st
  | CAssn assn c =>
    sample: st' <- do_assn defs assn st;
    run defs c st'
  | CIf e cthen celse c =>
    let branch := if feval_bexpr defs st e then cthen else celse in
    sample (run defs branch st) (run defs c)
  | CBlock vs block c =>
    sample: st' <- do_block vs (run defs block) st;
    run defs c st'
  end.

Lemma run_Assn defs assn c st :
  run defs (Assn assn;; c) st = run defs (CAssn assn c) st.
Proof.
rewrite /Assn /=; case: eqP=> [->|] //=.
by rewrite do_assn0 sample_diracL.
Qed.

Lemma run_Assn0 defs assn st :
  run defs (Assn assn) st = run defs (CAssn assn CSkip) st.
Proof. by rewrite -run_Assn Seqc1. Qed.

Lemma run_Block defs vs c st :
  run defs (Block vs c) st = run defs (CBlock vs c CSkip) st.
Proof.
rewrite /Block /=; case: eqP=> [->|_] //=.
  rewrite /= /do_block /= sampleA (_ : updm _ _ = st).
    rewrite -[LHS]sample_diracR; apply/eq_sample=> /= st'.
    by rewrite sample_diracL; congr dirac; apply/eq_ffun=> v; rewrite updmE /=.
  by apply/eq_ffun=> v /=; rewrite updmE /=.
case: eqP=> [->|] //=.
rewrite /do_block sampleA !sample_diracL; congr dirac.
apply/eq_ffun=> v; rewrite !updmE /= !mkfmapfE.
by case: ifP=> // ->.
Qed.

Lemma run_Seq defs c1 c2 st :
  run defs (c1;; c2) st =
  sample: st' <- run defs c1 st; run defs c2 st'.
Proof.
elim: c1 st=> /=.
- by move=> st; rewrite sample_diracL.
- move=> assn c1 IH st.
  rewrite [RHS]sampleA; apply/eq_sample=> /= st'.
  by rewrite IH.
- move=> e cthen _ celse _ c1 IH st; rewrite /= sampleA.
  apply/eq_sample=> st'; exact: IH.
- move=> vs c _ c' IH st; rewrite (lock do_block) sampleA.
  apply/eq_sample=> st'; exact: IH.
Qed.

Lemma run_DAssn defs σ c st :
  run defs (DAssn σ;; c) st
  = run defs c (do_subst defs σ st).
Proof. by rewrite run_Assn /= do_assnD sample_diracL. Qed.

(*
Lemma AssnC defs σ assn st :
  fdisjoint (subst_vars defs σ) (domm assn) ->
  run defs (DAssn σ;; Assn assn) st =
  run defs (Assn (subst_assn σ assn);;
            DAssn σ) st.
Proof.
move=> dis.
rewrite run_DAssn run_Assn0 /= run_Assn /=.
rewrite /subst_assn.
under [in RHS] eq_mapm_p=> pe /=.
  rewrite sampleA.
  under eq_sample=> e.
    rewrite sample_diracL subst_zexprP.
    under eq_eval_zexpr=> v.
      have ->: eval_zexpr st (mkffunm ZVar dassn v) = flush id st dassn v.
        by rewrite mkffunmE flushE; case: (dassn v).
      over.
    over.
  over.
apply: eq_in_sample=> /= vals /supp_mapm_pP [/= edomm ecodomm].
rewrite -[DAssn dassn]Seqc1 run_DAssn /=; congr dirac.
apply/eq_ffun=> v; rewrite !(updmE, mapmE).
case dassn_v: (dassn v)=> [e|] //=.
*)

Fixpoint com_mod_vars c : {fset var} :=
  match c with
  | CSkip => fset0
  | CAssn assn c => domm assn :|: com_mod_vars c
  | CIf _ cthen celse c => com_mod_vars cthen :|: com_mod_vars celse :|: com_mod_vars c
  | CBlock vs block c => (com_mod_vars block :\: vs) :|: com_mod_vars c
  end.

Definition modifies (f : state -> {prob state}) vs :=
  forall st st' v, st' \in supp (f st) -> v \notin vs -> st' v = st v.

Lemma modifiesW f vs vs' :
  fsubset vs' vs ->
  modifies f vs' ->
  modifies f vs.
Proof.
move=> sub mod st st' v st'_f v_vs; apply: mod=> //.
apply: contra v_vs; exact/fsubsetP.
Qed.

Lemma do_block_mod vs locals block :
  modifies block vs ->
  modifies (do_block locals block) (vs :\: locals).
Proof.
move=> mod_block st st'' v /supp_sampleP [st' st'P /supp_diracP ->].
rewrite updmE mkfmapfE in_fsetD negb_and negbK.
have [//|v_locals v_vs] := boolP (v \in locals).
by rewrite (mod_block _ _ _ st'P v_vs) updmE mkfmapfE (negbTE v_locals).
Qed.

Lemma com_mod_varsP defs c : modifies (run defs c) (com_mod_vars c).
Proof.
elim: c.
- by move=> /= st st' v /supp_diracP ->.
- move=> /= assn c IH st st'' v.
  case/supp_sampleP=> st' /do_assnP-/(_ v).
  rewrite in_fsetU negb_or mem_domm.
  by case assn_v: (assn v)=> //= <-; eauto.
- move=> /= e cthen IHthen celse IHelse c IH st st'' v.
  case/supp_sampleP=> st' st'_supp st''_supp.
  rewrite !in_fsetU !negb_or -andbA; case/and3P=> cthenP celseP cP.
  rewrite (IH _ _ _ st''_supp) //.
  by case: (feval_bexpr defs st e) st'_supp=> ?; eauto.
- move=> /= vs block IHblock c IHc st st'' v.
  case/supp_sampleP=> st' st'_supp st''_supp.
  rewrite in_fsetU; case/norP=> v_block v_c.
  rewrite (IHc _ _ _ st''_supp v_c).
  exact: do_block_mod st'_supp v_block.
Qed.

Fixpoint com_read_vars defs c :=
  match c with
  | CSkip =>
    fset0
  | CAssn assn c =>
    \bigcup_(p <- codomm assn)
      \bigcup_(e <- supp p) zexpr_vars defs e
    :|: (com_read_vars defs c :\: domm assn)
  | CIf e cthen celse c =>
    bexpr_vars defs e
    :|: com_read_vars defs cthen
    :|: com_read_vars defs celse
    :|: com_read_vars defs c
  | CBlock vs block c =>
    (com_read_vars defs block :\: vs)
    :|: com_read_vars defs c
  end.

Lemma com_read_varsP defs c st1 st2 :
  let R vs st1 st2 := {in vs, st1 =1 st2} in
  forall vs, fsubset (com_read_vars defs c) vs ->
  R vs st1 st2 ->
  coupling (R vs) (run defs c st1) (run defs c st2).
Proof.
move=> R; elim: c st1 st2.
- move=> /= st1 st2 vs _ e; exact: coupling_dirac.
- move=> /= assn c IH st1 st2 vs.
  rewrite fsubUset fsubDset; case/andP=> sub_assn sub_c R12.
  suff H : coupling (R (domm assn :|: vs)) (do_assn defs assn st1) (do_assn defs assn st2).
    apply: coupling_sample H _ => st1' st2' _ _ R12'.
    move/(IH _ _ _ sub_c): R12'; apply: couplingW.
    by move=> {}st1' {}st2' R12' v v_vs; apply: R12'; apply/fsetUP; right.
  pose u st exps := updm st (mapm (feval_zexpr defs st) exps).
  exists (sample: exps <- mapm_p id assn; dirac (u st1 exps, u st2 exps)).
  + by rewrite sampleA; apply/eq_sample=> exps; rewrite sample_diracL.
  + by rewrite sampleA; apply/eq_sample=> exps; rewrite sample_diracL.
  case=> _ _ /supp_sampleP [exps /supp_mapm_pP [ed es] /supp_diracP [-> ->]].
  move=> v; rewrite /= !updmE !mapmE in_fsetU ed mem_domm.
  case exps_v: (exps v)=> [e|] /=; last exact: R12.
  have /dommP [p assn_v] : v \in domm assn by rewrite ed mem_domm exps_v.
  have e_p := es _ _ _ assn_v exps_v.
  have assn_p : p \in codomm assn by apply/codommP; exists v.
  have {}sub_assn: fsubset (zexpr_vars defs e) vs.
    move/bigcupS/(_ _ assn_p erefl): sub_assn.
    by move/bigcupS/(_ _ e_p erefl).
  move=> _; apply/eq_in_feval_zexpr=> ? in_e; apply: R12.
  by move: in_e; apply/fsubsetP.
- move=> /= e cthen IHthen celse IHelse c IHc st1 st2 vs.
  rewrite !fsubUset -!andbA; case/and4P=> sub_e sub_then sub_else sub_c R12.
  set b := feval_bexpr defs st2 e.
  have eb: feval_bexpr defs st1 e = b.
    apply/eq_in_feval_bexpr=> v v_in; apply: R12.
    by apply/fsubsetP: v_in.
  rewrite eb; set cb := if b then cthen else celse.
  suff H : coupling (R vs) (run defs cb st1) (run defs cb st2).
    apply: coupling_sample H _ => st1' st2' _ _; exact: IHc.
  by rewrite /cb; case: (b); [apply: IHthen|apply: IHelse].
- move=> /= vs' block IHblock c IHc st1 st2 vs.
  rewrite fsubUset fsubDset; case/andP=> sub_block sub_c R12.
  rewrite 2!do_blockE /=.
  pose rb st := run defs block (updm st (mkfmapf (fun=> 0%R) vs')).
  have H1 : coupling (R (vs' :|: vs)) (rb st1) (rb st2).
    apply: IHblock=> // v; rewrite !updmE mkfmapfE.
    rewrite in_fsetU; case: ifP=> //= _; exact: R12.
  apply: coupling_sample H1 _ => st1' st2' _ _ R12'.
  pose rest st st' : state := updm st' (mkfmapf st vs').
  have R12'' : R vs (rest st1 st1') (rest st2 st2').
    move=> v v_vs; rewrite !updmE !mkfmapfE.
    case: ifP=> _; [apply: R12|apply: R12']=> //.
    by apply/fsetUP; right.
  exact: IHc.
Qed.

(* Find out which variables are needed to compute some portion of the state *)
Fixpoint com_used_vars (vs : {fset var}) defs c :=
  match c with
  | CSkip => vs
  | CAssn assn c =>
    \bigcup_(v <- com_used_vars vs defs c)
       if assn v is Some p then \bigcup_(e <- supp p) zexpr_vars defs e
       else fset1 v
  | CIf e cthen celse c =>
    let vs := com_used_vars vs defs c in
    bexpr_vars defs e
    :|: com_used_vars vs defs cthen
    :|: com_used_vars vs defs celse
  | CBlock locals block c =>
    let vs' := com_used_vars vs defs c in
    let reset := locals :&: vs' in
    com_used_vars (vs' :\: locals) defs block :\: locals :|: reset
  end.

Lemma com_used_varsP vs defs c st1 st2 :
  let R vs st1 st2 := {in vs, st1 =1 st2} in
  R (com_used_vars vs defs c) st1 st2 ->
  coupling (R vs) (run defs c st1) (run defs c st2).
Proof.
move=> R; elim: c vs st1 st2.
- by move=> /= vs st1 st2 R12; apply: coupling_dirac.
- move=> /= assn c IH vs st1 st2 R12.
  pose pu st := do_assn defs assn st.
  suff H : coupling (R (com_used_vars vs defs c)) (pu st1) (pu st2).
    by apply: coupling_sample H _; eauto.
  pose u st exps := updm st (mapm (feval_zexpr defs st) exps).
  exists (sample: exps <- mapm_p id assn; dirac (u st1 exps, u st2 exps)).
  + by rewrite sampleA; apply/eq_sample=> exps; rewrite sample_diracL.
  + by rewrite sampleA; apply/eq_sample=> exps; rewrite sample_diracL.
  case=> _ _ /supp_sampleP [exps /supp_mapm_pP [ed es] /supp_diracP [-> ->]].
  move=> v v_vs; rewrite /= !updmE !mapmE.
  case exps_v: (exps v)=> [e|] /=; last first.
    have /dommPn assn_v : v \notin domm assn by rewrite ed mem_domm exps_v.
    by apply: R12; apply/bigcupP; exists v; rewrite // assn_v in_fset1 eqxx.
  have /dommP [p assn_v] : v \in domm assn by rewrite ed mem_domm exps_v.
  have e_p := es _ _ _ assn_v exps_v.
  apply/eq_in_feval_zexpr=> v' v'P; apply: R12.
  apply/bigcupP; exists v; rewrite // assn_v.
  by apply/bigcupP; exists e.
- move=> /= e cthen IHthen celse IHelse c IHc vs st1 st2 R12.
  set vs' := com_used_vars vs defs c in R12 *.
  set b := feval_bexpr defs st2 e.
  have eb: feval_bexpr defs st1 e = b.
    apply/eq_in_feval_bexpr=> v v_in; apply: R12; by rewrite !in_fsetU v_in.
  rewrite eb; set cb := if b then cthen else celse.
  suff H : coupling (R vs') (run defs cb st1) (run defs cb st2).
    apply: coupling_sample H _ => st1' st2' _ _ ; exact: IHc.
  have R12then : R (com_used_vars vs' defs cthen) st1 st2.
    by move=> v v_in; apply: R12; rewrite !in_fsetU v_in /= orbT.
  have R12else : R (com_used_vars vs' defs celse) st1 st2.
    by move=> v v_in; apply: R12; rewrite !in_fsetU v_in /= orbT.
  by rewrite /cb; case: (b); [apply: IHthen|apply: IHelse].
- move=> /= locals block IHblock c IHc vs st1 st2 R12.
  set vs' := com_used_vars vs defs c in R12 *.
  set reset := locals :&: vs' in R12 *.
  set vs'' := com_used_vars (vs' :\: locals) defs block in R12 *.
  pose u st : state := updm st (mkfmapf (fun=> 0%R) locals).
  have R12' : R vs'' (u st1) (u st2).
    move=> v v_vs'; rewrite !updmE mkfmapfE; case: ifPn=> // v_locals.
    by apply: R12; apply/fsetUP; left; apply/fsetDP.
  have {}R12' := IHblock _ _ _ R12'.
  rewrite 2!do_blockE /=.
  apply: coupling_sample R12' _ => st1' st2' _ _ {}R12'.
  apply: IHc; rewrite -/vs' => v v_vs'; rewrite !updmE !mkfmapfE.
  case: ifPn => v_locals.
    by apply: R12; rewrite in_fsetU /reset in_fsetI v_vs' v_locals orbT.
  by apply: R12'; apply/fsetDP.
Qed.

Definition match_prob vs1 vs2 f g :=
  forall st1 st2,
    {in vs1, st1 =1 st2} ->
    coupling (fun st1' st2' => {in vs2, st1' =1 st2'}) (f st1) (g st2).

Lemma match_probWL vs1' vs1 vs2 f g :
  fsubset vs1 vs1' ->
  match_prob vs1 vs2 f g ->
  match_prob vs1' vs2 f g.
Proof.
move=> sub efg st1 st2 est; apply: efg=> v v_vs; apply: est.
by apply/fsubsetP: v_vs.
Qed.

Definition dependencies := ffun (fun v : var => fset1 v).
Implicit Types deps : dependencies.

Definition lift_deps deps vs := \bigcup_(v <- vs) deps v.

Lemma fsubset_lift_deps deps1 deps2 vs :
  (forall v, v \in vs -> fsubset (deps1 v) (deps2 v)) ->
  fsubset (lift_deps deps1 vs) (lift_deps deps2 vs).
Proof.
move=> sub; apply/fsubsetP=> v /bigcupP [] v' v'_vs _ v_v'.
apply/bigcupP; exists v'=> //; apply/fsubsetP: v_v'; exact: sub.
Qed.

Definition deps_spec deps f :=
  forall vs, match_prob (lift_deps deps vs) vs f f .

Lemma deps_specW deps1 deps2 f :
  (forall v, fsubset (deps1 v) (deps2 v)) ->
  deps_spec deps1 f ->
  deps_spec deps2 f.
Proof.
move=> deps12 deps1P vs st1 st2 R12.
apply: deps1P=> v' /bigcupP [] v v_vs _ /(fsubsetP (deps12 v)) v'_v.
by apply: R12; apply/bigcupP; exists v.
Qed.

Definition deps_comp deps deps' : dependencies :=
  mkffun (fun v => lift_deps deps (deps' v))
         (supp deps :|: supp deps').

Lemma lift_deps_deps_comp deps deps' vs :
  lift_deps (deps_comp deps deps') vs =
  lift_deps deps (lift_deps deps' vs).
Proof.
apply/eq_fset=> v; apply/(sameP bigcupP)/(iffP bigcupP).
- case=> v' /bigcupP [] v'' v''_vs _ v'_v'' _ v_v'.
  exists v''; rewrite // mkffunE; case: ifPn.
    by move=> _; apply/bigcupP; exists v'.
  rewrite in_fsetU; case/norP=> /suppPn e'' /suppPn e'; rewrite -e''.
  by move: v'_v'' v_v'; rewrite e'=> /fset1P ->.
- case=> v'' v''_vs _; rewrite mkffunE; case: ifPn.
    move=> _; case/bigcupP=> v' v'_v'' _ v_v'.
    by exists v'=> //; apply/bigcupP; exists v''.
  rewrite in_fsetU; case/norP=> /suppPn e'' /suppPn e' /fset1P e.
  move: e' e'' v''_vs; rewrite -{}e {v''}=> e' e'' v_vs.
  exists v; rewrite ?e'' ?in_fset1 //.
  by apply/bigcupP; exists v; rewrite ?e' ?in_fset1.
Qed.

Lemma supp_deps_comp deps deps' :
  fsubset (supp (deps_comp deps deps')) (supp deps :|: supp deps').
Proof. exact: supp_mkffun_subset. Qed.

Lemma deps_compP deps_f deps_g f g :
  deps_spec deps_f f  ->
  deps_spec deps_g g ->
  deps_spec (deps_comp deps_f deps_g) (fun st => sample (f st) g).
Proof.
move=> fP gP vs st1 st2 e12.
set vs_g := \bigcup_(v <- vs) deps_g v.
set vs_f := \bigcup_(v <- vs_g) deps_f v.
suff vs_fE : vs_f = lift_deps (deps_comp deps_f deps_g) vs.
  move: e12; rewrite -vs_fE=> /fP e12.
  by apply: coupling_sample e12 _ => st1' st2' _ _ /gP.
apply/eqP; rewrite eqEfsubset; apply/andP; split.
- apply/bigcupS=> v /bigcupP [] v' v'_vs _ v_v' _.
  apply/fsubsetP=> v'' v''_v; apply/bigcupP; exists v'=> //.
  rewrite /deps_comp mkffunE; case: ifPn; last first.
    rewrite in_fsetU; case/norP=> v'_f v'_g.
    move: v_v'; rewrite (suppPn v'_g) => /fset1P e.
    by rewrite -(suppPn v'_f) -e.
  by move=> ?; apply/bigcupP; exists v.
- apply/bigcupS=> v v_vs _; apply/fsubsetP=> v'.
  rewrite /deps_comp mkffunE; case: ifPn.
    move=> _ /bigcupP [] v'' v''_v _ v'_v''.
    by apply/bigcupP; exists v''=> //; apply/bigcupP; exists v.
  rewrite in_fsetU; case/norP=> /suppPn v_f /suppPn v_g /fset1P ->.
  rewrite /vs_f /vs_g.
  apply/bigcupP; exists v; rewrite ?v_f ?in_fset1 ?eqxx //.
  apply/bigcupP; exists v; rewrite ?v_g ?in_fset1 ?eqxx //.
Qed.

Definition assn_deps defs assn : dependencies :=
  let def v := if assn v is Some p then
                 \bigcup_(e <- supp p) zexpr_vars defs e
               else fset1 v in
  mkffun def (domm assn).

Lemma assn_depsP defs assn1 assn2 vs :
  {in vs, assn1 =1 assn2} ->
  match_prob (lift_deps (assn_deps defs assn1) vs) vs
             (do_assn defs assn1) (do_assn defs assn2).
Proof.
move=> eassn st1 st2 est.
apply: coupling_sample; first by apply: coupling_mapm_p_eq; exact: eassn.
move=> es1 es2 es1P es2P /= ees; apply: coupling_dirac=> v v_vs.
case/supp_mapm_pP: es1P=> ed1 es1P.
rewrite !updmE !mapmE -ees //; case es_v: (es1 v)=> [e|] /=.
  apply/eq_in_feval_zexpr=> v' v'_e; apply: est.
  apply/bigcupP; exists v; rewrite // mkffunE mem_domm.
  have: assn1 v by rewrite -mem_domm ed1 mem_domm es_v.
  case assn_v: (assn1 v)=> [p|] //= _.
  by apply/bigcupP; exists e; rewrite // (es1P _ _ _ assn_v).
apply: est; apply/bigcupP; exists v; rewrite // mkffunE.
by rewrite ed1 mem_domm es_v in_fset1.
Qed.

Definition if_deps defs e deps_then deps_else mod : dependencies :=
  let ve := bexpr_vars defs e in
  let deps_b v := ve :|: deps_then v :|: deps_else v in
  mkffun (fun v => ve :|: deps_then v :|: deps_else v) mod.

Lemma if_depsP defs e dt ft1 ft2 de fe1 fe2 mod vs :
  match_prob (lift_deps dt vs) vs ft1 ft2 ->
  match_prob (lift_deps de vs) vs fe1 fe2 ->
  fsubset (supp dt) mod -> fsubset (supp de) mod ->
  modifies ft1 mod -> modifies ft2 mod -> modifies fe1 mod -> modifies fe2 mod ->
  match_prob (lift_deps (if_deps defs e dt de mod) vs) vs
             (fun st => if feval_bexpr defs st e then ft1 st else fe1 st)
             (fun st => if feval_bexpr defs st e then ft2 st else fe2 st).
Proof.
move=> dtP deP dt_mod de_mod ft1_mod ft2_mod fe1_mod fe2_mod.
pose ite ft fe st : {prob state} :=
  if feval_bexpr defs st e then ft st else fe st.
rewrite -/(ite ft1 fe1) -/(ite ft2 fe2).
have f1_mod : modifies (ite ft1 fe1) mod.
  by move=> st st' v; rewrite /ite; case: ifP=> _; eauto.
have f2_mod : modifies (ite ft2 fe2) mod.
  by move=> st st' v; rewrite /ite; case: ifP=> _; eauto.
move=> st1 st2 est.
have [dis|not_dis] := boolP (fdisjoint vs mod).
  have evs : lift_deps (if_deps defs e dt de mod) vs = vs.
    rewrite /lift_deps big_seq.
    under eq_big=> [v|v v_vs]; first over.
      rewrite mkffunE ifF; last exact/negbTE/(fdisjointP dis).
      over.
    by rewrite -big_seq bigcup1 fsvalK.
  apply: coupling_trivial=> st1' st2' /f1_mod st1'P /f2_mod st2'P v v_vs.
  have ? : v \notin mod by apply/fdisjointP: v_vs.
  by rewrite st1'P ?st2'P ?est ?evs.
set vs' := lift_deps _ _ in est *.
have sub : fsubset (bexpr_vars defs e) vs'.
  have /fset0Pn [v /fsetIP [v_vs v_mod]] := not_dis.
  apply: fsubset_trans; last by apply: bigcup_sup; eauto.
  by rewrite mkffunE v_mod -fsetUA fsubsetUl.
have estW : {in bexpr_vars defs e, st1 =1 st2}.
  move=> v /(fsubsetP sub) v_vs; exact: est.
rewrite /ite; under eq_in_feval_bexpr => ?? do rewrite estW //.
have dtP' : match_prob vs' vs ft1 ft2.
  apply: match_probWL dtP; apply: fsubset_lift_deps=> v v_vs.
  rewrite mkffunE -fsetUA; case: ifPn=> v_mod.
    by rewrite fsubsetU ?fsubsetUl ?orbT.
  suff /suppPn -> : v \notin supp dt by rewrite fsubsetxx.
  by apply: contra v_mod; apply/fsubsetP.
have deP' : match_prob vs' vs fe1 fe2.
  apply: match_probWL deP; apply: fsubset_lift_deps=> v v_vs.
  rewrite mkffunE -fsetUA; case: ifPn=> v_mod.
    by rewrite fsubsetU ?fsubsetUr ?orbT.
  suff /suppPn -> : v \notin supp de by rewrite fsubsetxx.
  by apply: contra v_mod; apply/fsubsetP.
by case: feval_bexpr; eauto.
Qed.

Definition block_deps defs (locals : {fset var}) db : dependencies :=
  let deps_locals : dependencies := mkffun (fun=> fset0) locals in
  let deps_block  := deps_comp deps_locals db in
  mkffun deps_block (supp deps_block :\: locals).

Lemma block_depsP defs locals db vs block1 block2 :
  match_prob (lift_deps db (vs :\: locals)) (vs :\: locals) block1 block2 ->
  match_prob (lift_deps (block_deps defs locals db) vs) vs
             (do_block locals block1)
             (do_block locals block2).
Proof.
rewrite /do_block /block_deps; move=> eb st1 st2.
set reset := mkffun (fun=> fset0) locals.
set deps_block1 := deps_comp reset db.
set deps_block2 := mkffun deps_block1 _.
set zeroed := mkfmapf (fun=> 0%R) locals.
pose zero st := updm st zeroed => est.
have est': {in lift_deps deps_block1 (vs :\: locals), st1 =1 st2}.
  move=> v /bigcupP [] v' /fsetDP [v'_vs v'_locals] _ v_v'; apply: est.
  apply/bigcupP; exists v'; rewrite // mkffunE.
  case: ifPn=> //; rewrite in_fsetD negb_and negbK.
  by rewrite (negbTE v'_locals) => /suppPn <-.
rewrite lift_deps_deps_comp in est'.
have {}est': {in lift_deps db (vs :\: locals), zero st1 =1 zero st2}.
  move=> v v_vs; rewrite !updmE !mkfmapfE; case: ifP=> // v_locals.
  by apply: est'; apply/bigcupP; exists v; rewrite // mkffunE v_locals in_fset1.
apply: coupling_sample (eb _ _ est') _ => st1' st2' _ _ {}est'.
apply: coupling_dirac=> v v_vs; rewrite !updmE !mkfmapfE.
case: ifP=> v_locals; last by apply: est'; rewrite in_fsetD v_locals.
apply: est.
by apply/bigcupP; exists v; rewrite // mkffunE in_fsetD v_locals in_fset1.
Qed.

Fixpoint com_deps defs c : dependencies :=
  match c with
  | CSkip => emptyf
  | CAssn assn c =>
    let deps_c := com_deps defs c in
    deps_comp (assn_deps defs assn) deps_c
  | CIf e cthen celse c =>
    let deps_then := com_deps defs cthen in
    let deps_else := com_deps defs celse in
    let mod := com_mod_vars cthen :|: com_mod_vars celse in
    let deps_b := if_deps defs e deps_then deps_else mod in
    deps_comp deps_b (com_deps defs c)
  | CBlock locals block c =>
    deps_comp (block_deps defs locals (com_deps defs block)) (com_deps defs c)
  end.

Lemma supp_com_deps defs c : fsubset (supp (com_deps defs c)) (com_mod_vars c).
Proof.
elim: c.
- by rewrite /= supp0 fsubsetxx.
- move=> /= assn c IH.
  apply: fsubset_trans (supp_deps_comp _ _) _.
  apply: fsetUSS=> //; exact: supp_mkffun_subset.
- move=> /= b cthen IHthen celse IHelse c IHc.
  apply: fsubset_trans (supp_deps_comp _ _) _.
  apply: fsetUSS=> //; exact: supp_mkffun_subset.
- move=> /= locals block IHblock c IHc.
  apply: fsubset_trans (supp_deps_comp _ _) _.
  apply: fsetUSS=> //.
  apply: fsubset_trans (supp_mkffun_subset _ _ _) _.
  rewrite fsubDset fsetUDr fsetDv fsetD0.
  apply: fsubset_trans (supp_deps_comp _ _) _.
  by rewrite fsetUSS // supp_mkffun_subset.
Qed.

Lemma com_depsP defs c : deps_spec (com_deps defs c) (run defs c).
Proof.
elim: c.
- move=> /= vs st1 st2.
  rewrite (_ : lift_deps emptyf vs = vs); last first.
    apply/eq_fset=> v; apply/(sameP bigcupP)/(iffP idP).
    + by move=> v_vs; exists v; rewrite ?emptyfE ?in_fset1.
    + by case=> v' v'_vs _; rewrite emptyfE => /fset1P ->.
  exact: coupling_dirac.
- move=> /= assn c IH; apply: deps_compP=> // vs st1 st2 e12.
  exact: assn_depsP.
- move=> /= e cthen IHthen celse IHelse c IHc.
  apply: deps_compP=> // vs st1 st2.
  set deps_then := com_deps defs cthen.
  set deps_else := com_deps defs celse.
  set mod := com_mod_vars cthen :|: com_mod_vars celse.
  rewrite 2!fun_if 2!if_arg.
  have mod_then : modifies (run defs cthen) mod.
    apply: modifiesW (@com_mod_varsP _ _); exact: fsubsetUl.
  have mod_else : modifies (run defs celse) mod.
    apply: modifiesW (@com_mod_varsP _ _); exact: fsubsetUr.
  by apply: if_depsP; rewrite // fsubsetU // supp_com_deps ?orbT.
- move=> locals block IHblock c IHc /=.
  apply: deps_compP=> // vs st1 st2.
  exact: block_depsP.
Qed.

Fixpoint live_vars_loop k deps (vs : {fset var}) :=
  if k is k.+1 then
    let next := \bigcup_(v <- vs) deps v in
    if fsubset next vs then vs else live_vars_loop k deps (vs :|: next)
  else vs.

Lemma fsubset_live_vars_loop k deps vs : fsubset vs (live_vars_loop k deps vs).
Proof.
elim: k vs=> [|k IH] //= vs; first exact: fsubsetxx.
case: ifP=> _; rewrite ?fsubsetxx //.
by apply: fsubset_trans (IH _); rewrite fsubsetUl.
Qed.

Lemma live_vars_loopP k deps vs0 vs :
  size (vs :\: vs0) <= k ->
  fsubset vs0 vs ->
  (forall v, v \in vs -> fsubset (deps v) vs) ->
  let fp := live_vars_loop k deps vs0 in
  fp = fp :|: lift_deps deps fp.
Proof.
move=> hsize sub_vs sub_deps fp.
elim: k vs0 @fp hsize sub_vs=> [|k IH] vs0.
  rewrite /= leqn0 sizes_eq0 -fsubset0 fsubDset fsetU0.
  move=> sub1 sub2; have -> : vs0 = vs.
    by apply/eqP; rewrite eqEfsubset sub2.
  apply/esym/fsetUidPl/fsubsetP=> v /bigcupP [] v' v'_vs _.
  apply/fsubsetP; exact: sub_deps.
rewrite [live_vars_loop _ _ _]/=.
set next := \bigcup_(v <- vs0) deps v.
have [sub_next /= _ _|not_sub] := boolP (fsubset next vs0).
  exact/esym/fsetUidPl.
move=> fp hsize sub_vs.
have sub_next : fsubset next vs.
  apply/bigcupS=> v /(fsubsetP sub_vs) v_vs _.
  exact: sub_deps.
have /fset0Pn [v /fsetDP [v_next v_vs0]] : next :\: vs0 != fset0.
  by rewrite -fsubset0 fsubDset fsetU0.
have leq_size : size (vs :\: (vs0 :|: next)) < size (vs :\: vs0).
  rewrite [in X in _ < X](sizesD1 v) in_fsetD.
  rewrite v_vs0 (fsubsetP sub_next _ v_next) ltnS.
  by rewrite fsubset_leq_size ?fsetDDl ?fsetDS ?fsetUS ?fsub1set.
apply: IH; first exact: leq_trans leq_size hsize.
by rewrite fsubUset sub_vs.
Qed.

Definition live_vars defs c vs0 :=
  let deps := com_deps defs c in
  let vs   := vs0 :|: lift_deps deps (supp deps) in
  live_vars_loop (size vs) deps vs0.

Lemma fsubset_live_vars defs c vs0 : fsubset vs0 (live_vars defs c vs0).
Proof. exact: fsubset_live_vars_loop. Qed.

Lemma live_varsP defs c vs0 :
  let deps := com_deps defs c in
  let vs := live_vars defs c vs0 in
  vs = vs :|: lift_deps deps vs.
Proof.
move=> deps; rewrite /live_vars -/deps; set vs := vs0 :|: _.
apply: (@live_vars_loopP _ _ _ vs).
- by rewrite fsubset_leq_size // fsubDset fsubsetUr.
- exact: fsubsetUl.
move=> v v_vs; apply/fsubsetP=> v' v'_deps.
have [v_supp|v_supp] := boolP (v \in supp deps).
  by apply/fsetUP; right; apply/bigcupP; exists v.
by move: v'_deps; rewrite (suppPn v_supp) => /fset1P ->.
Qed.

Fixpoint dead_store_elim_loop defs c live :=
  match c with
  | CSkip => CSkip
  | CAssn assn c =>
    let live' := lift_deps (com_deps defs c) live      in
    let assn' := filterm (fun v _ => v \in live') assn in
    let c'    := dead_store_elim_loop defs c live           in
    CAssn assn' c'
  | CIf e cthen celse c =>
    let live'  := lift_deps (com_deps defs c) live in
    let cthen' := dead_store_elim_loop defs cthen live' in
    let celse' := dead_store_elim_loop defs celse live' in
    let c'     := dead_store_elim_loop defs c live      in
    CIf e cthen' celse' c'
  | CBlock locals block c =>
    let live'  := lift_deps (com_deps defs c) live  in
    let live'' := live' :\: locals                  in
    let block' := dead_store_elim_loop defs block live'' in
    let c'     := dead_store_elim_loop defs c live       in
    CBlock locals block' c'
  end.

Lemma dead_store_elim_loop_com_mod_vars defs c live :
  fsubset (com_mod_vars (dead_store_elim_loop defs c live)) (com_mod_vars c).
Proof.
by elim: c live => *; rewrite /= ?fsetUSS ?fsubsetxx ?domm_filter ?fsetSD.
Qed.

Lemma dead_store_elim_loopP defs c live :
  let deps := com_deps defs c in
  let c' := dead_store_elim_loop defs c live in
  match_prob (lift_deps deps live) live (run defs c) (run defs c').
Proof.
elim: c live.
- move=> /= live st1 st2 est; apply: coupling_dirac=> v v_live.
  by apply: est; apply/bigcupP; exists v; rewrite // emptyfE in_fset1.
- move=> /= assn c IH live st1 st2; rewrite lift_deps_deps_comp=> est.
  set live' := lift_deps _ live in est; apply: coupling_sample.
    apply: assn_depsP est; rewrite -/live' => v v_live'.
    by rewrite filtermE v_live'; case: (assn v).
  move=> st1' st2' _ _; exact: IH.
- move=> /= e cthen IHthen celse IHelse c IHc live st1 st2.
  rewrite lift_deps_deps_comp; set live' := lift_deps _ live=> est.
  apply: coupling_sample; last by move=> st1' st2' _ _; exact: IHc.
  rewrite 2!fun_if 2!if_arg; apply: (if_depsP (IHthen _) (IHelse _)) est;
  do 1?[apply: modifiesW (@com_mod_varsP _ _)];
  by rewrite ?fsubsetUl ?fsubsetUr ?fsubsetU ?dead_store_elim_loop_com_mod_vars
             ?supp_com_deps ?orbT.
- move=> /= locals block IHblock c IHc live st1 st2.
  rewrite lift_deps_deps_comp=> est.
  apply: coupling_sample.
    by apply: block_depsP; first exact: IHblock; eauto.
  move=> ????; exact: IHc.
Qed.

Definition dead_store_elim defs c vs :=
  let live := live_vars defs c vs in
  dead_store_elim_loop defs c live.

Lemma dead_store_elimP defs c vs :
  let live := live_vars defs c vs in
  let c'   := dead_store_elim defs c vs in
  match_prob live live (run defs c) (run defs c').
Proof.
move=> live c'; rewrite {1}/live live_varsP.
apply: match_probWL (fsubsetUr _ _) _.
exact: dead_store_elim_loopP.
Qed.

Inductive mcom T :=
| MSkip
| MAssn of assignment & mcom T & T
| MIf of bexpr & mcom T & T & mcom T & T & mcom T & T
| MBlock of {fset var} & mcom T & T & mcom T & T.
Arguments MSkip {T}.

Fixpoint mcom_proj T (mc : mcom T) :=
  match mc with
  | MSkip => CSkip
  | MAssn assn mc _ => CAssn assn (mcom_proj mc)
  | MIf e mcthen _ mcelse _ mc _ => CIf e (mcom_proj mcthen) (mcom_proj mcelse) (mcom_proj mc)
  | MBlock locals mblock _ mc _ => CBlock locals (mcom_proj mblock) (mcom_proj mc)
  end.

Fixpoint dead_store_elim_opt_init defs c : mcom dependencies * dependencies * {fset var} :=
  match c with
  | CSkip => (MSkip, emptyf, fset0)
  | CAssn assn c =>
    let: (mc, deps_c, mod_c) := dead_store_elim_opt_init defs c in
    (MAssn assn mc deps_c,
     deps_comp (assn_deps defs assn) deps_c,
     domm assn :|: mod_c)
  | CIf e cthen celse c =>
    let: (mcthen, deps_then, mod_then) := dead_store_elim_opt_init defs cthen in
    let: (mcelse, deps_else, mod_else) := dead_store_elim_opt_init defs celse in
    let: (mc, deps_c, mod_c) := dead_store_elim_opt_init defs c in
    let deps_b := if_deps defs e deps_then deps_else (mod_then :|: mod_else) in
    (MIf e mcthen deps_then mcelse deps_else mc deps_c,
     deps_comp deps_b deps_c,
     mod_then :|: mod_else :|: mod_c)
  | CBlock locals block c =>
    let: (mblock, deps_block, mod_block) := dead_store_elim_opt_init defs block in
    let: (mc, deps_c, mod_c) := dead_store_elim_opt_init defs c in
    (MBlock locals mblock deps_block mc deps_c,
     deps_comp (block_deps defs locals deps_block) deps_c,
     mod_block :\: locals :|: mod_c)
  end.

Fixpoint dead_store_elim_opt_init_spec defs c : mcom dependencies :=
  match c with
  | CSkip =>
    MSkip
  | CAssn assn c =>
    MAssn assn (dead_store_elim_opt_init_spec defs c) (com_deps defs c)
  | CIf e cthen celse c =>
    MIf e
        (dead_store_elim_opt_init_spec defs cthen) (com_deps defs cthen)
        (dead_store_elim_opt_init_spec defs celse) (com_deps defs celse)
        (dead_store_elim_opt_init_spec defs c)     (com_deps defs c)
  | CBlock locals block c =>
    MBlock locals
           (dead_store_elim_opt_init_spec defs block) (com_deps defs block)
           (dead_store_elim_opt_init_spec defs c) (com_deps defs c)
  end.

Lemma dead_store_elim_opt_initE defs c :
  dead_store_elim_opt_init defs c =
  (dead_store_elim_opt_init_spec defs c,
   com_deps defs c, com_mod_vars c).
Proof.
elim: c=> //= *;
by repeat match goal with
| [H : ?x = (_, _, _) |- context[?x]] => rewrite {}H /=
end.
Qed.

Fixpoint dead_store_elim_opt_loop mc live : com :=
  match mc with
  | MSkip => CSkip
  | MAssn assn mc deps_c =>
    let live' := lift_deps deps_c live in
    let assn' := filterm (fun v _ => v \in live') assn in
    let c'    := dead_store_elim_opt_loop mc live in
    CAssn assn' c'
  | MIf e mcthen deps_then mcelse deps_else mc deps_c =>
    let live' := lift_deps deps_c live in
    let cthen' := dead_store_elim_opt_loop mcthen live' in
    let celse' := dead_store_elim_opt_loop mcelse live' in
    let c' := dead_store_elim_opt_loop mc live in
    CIf e cthen' celse' c'
  | MBlock locals mblock deps_block mc deps_c =>
    let live' := lift_deps deps_c live in
    let live'' := live' :\: locals in
    let block' := dead_store_elim_opt_loop mblock live'' in
    let c' := dead_store_elim_opt_loop mc live in
    CBlock locals block' c'
  end.

Lemma dead_store_elim_opt_loopE defs c live :
  dead_store_elim_opt_loop (dead_store_elim_opt_init_spec defs c) live =
  dead_store_elim_loop defs c live.
Proof.
elim: c live=> //= *;
by repeat match goal with
| [H : forall live, ?f live = _
   |- context[?f ?live]] => rewrite {}H /=
end.
Qed.

Definition dead_store_elim_opt defs c vs0 :=
  let: (mc, deps_c, _) := dead_store_elim_opt_init defs c in
  let  vs := vs0 :|: lift_deps deps_c (supp deps_c) in
  let  live := live_vars_loop (size vs) deps_c vs0 in
  dead_store_elim_opt_loop mc live.

Lemma dead_store_elim_optE defs c vs0 :
  dead_store_elim_opt defs c vs0 =
  dead_store_elim     defs c vs0.
Proof.
rewrite /dead_store_elim_opt /dead_store_elim.
by rewrite dead_store_elim_opt_initE dead_store_elim_opt_loopE.
Qed.

Module Inlining.

Module Type CONFLICTS.
Parameter conflicts :
  subst -> {fset var} -> {fset var}.
Parameter conflicts_sub :
  forall σ vs, fsubset vs (conflicts σ vs).
Parameter conflicts_dis :
  forall σ vs v,
  v \in supp σ -> v \notin conflicts σ vs ->
  fdisjoint (zexpr_vars [::] (σ v)) (conflicts σ vs).
End CONFLICTS.

Module Export Conflicts : CONFLICTS.

Fixpoint loop k σ acc rem next :=
  if k is k.+1 then
    let has_conflict v := ~~ fdisjoint (zexpr_vars [::] (σ v)) next in
    let next' := fset_filter has_conflict rem in
    if next' == fset0 then acc
    else loop k σ (acc :|: next') (rem :\: next') next'
  else acc.

Definition conflicts σ vs :=
  loop (size (supp σ)) σ vs (supp σ :\: vs) vs.

Lemma loop_sub k σ acc rem next : fsubset acc (loop k σ acc rem next).
Proof.
elim: k acc rem next => /= [|k IH] acc rem next; first exact: fsubsetxx.
case: ifP=> _; first exact: fsubsetxx.
apply: fsubset_trans (IH _ _ _); exact: fsubsetUl.
Qed.

Lemma conflicts_sub σ vs : fsubset vs (conflicts σ vs).
Proof. exact: loop_sub. Qed.

Lemma loop_dis vs k σ acc next :
  let rem := supp σ :\: acc in
  let cs  := loop k σ acc rem next in
  size rem <= k ->
  fsubset next acc ->
  fsubset acc (supp σ :|: vs) ->
 (forall v, v \in rem -> fdisjoint (zexpr_vars [::] (σ v)) (acc :\: next)) ->
  forall v, v \in supp σ -> v \notin cs ->
    fdisjoint (zexpr_vars [::] (σ v)) cs.
Proof.
elim: k acc next=> [|k IH] acc next rem cs /=.
  rewrite leqn0 sizes_eq0=> /eqP /eq_fset e sub1 sub2 accP v v_σ.
  move/(_ v): e; rewrite in_fsetD v_σ andbT in_fset0.
  by rewrite /cs /= => ->.
rewrite {}/cs /=.
set has_conflict := fun v => ~~ fdisjoint _ _.
set next' := fset_filter has_conflict rem.
move=> size_rem sub1 sub2 accP v v_σ.
have acc_next: acc = acc :\: next :|: next.
  by rewrite -{1}(fsetID acc next) (fsetIidPr _ _ sub1) fsetUC.
case: (altP eqP)=> e.
  move=> v_loop; have v_rem : v \in rem by rewrite in_fsetD v_loop.
  rewrite acc_next fdisjointUr accP //.
  rewrite (_ : fdisjoint _ _ = (v \notin next')); first by rewrite e.
  by rewrite /next' in_fset_filter /rem in_fsetD v_loop v_σ !andbT negbK.
rewrite /rem fsetDDl.
set acc' := acc :|: next'.
set rem' := supp σ :\: acc'.
move=> v_loop.
have sub_rem : fsubset rem' rem by apply/fsetDS/fsubsetUl.
have {e} size_rem' : size rem' <= k.
  case/fset0Pn: e=> v' v'_next'.
  have v'_rem' : v' \notin rem'.
    by rewrite in_fsetD in_fsetU v'_next' orbT.
  have v'_rem : v' \in rem.
    by move: v'_next'; rewrite in_fset_filter; case/andP.
  have sub: fsubset rem' (rem :\ v').
    apply/fsubsetP=> v'' v''_rem'; rewrite in_fsetD1.
    rewrite (fsubsetP sub_rem) // andbT.
    by apply: contra v'_rem'=> /eqP <-.
  move/fsubset_leq_size in sub; apply: leq_trans sub _.
  by move: size_rem; rewrite [size rem](sizesD1 v') v'_rem.
have sub1' : fsubset next' acc' by exact: fsubsetUr.
have sub2' : fsubset acc' (supp σ :|: vs).
  apply/fsubsetP=> v'; case/fsetUP=> [/(fsubsetP sub2) //|].
  rewrite in_fset_filter in_fsetU; case/andP=> _.
  by case/fsetDP=> v'_σ _; rewrite v'_σ.
apply: IH=> // {}v {}v_σ {v_loop}.
have -> : acc' :\: next' = acc.
  rewrite fsetDUl fsetDv fsetU0.
  apply/eqP; rewrite eqEfsubset fsubDset fsubsetUr /=.
  apply/fsubsetP=> v' v'_acc.
  by rewrite in_fsetD in_fset_filter in_fsetD v'_acc andbF.
move: v_σ; rewrite fsetDUr -/rem; case/fsetIP=> v_rem /fsetDP [_ v_next'].
rewrite acc_next fdisjointUr accP //=.
by move: v_next'; rewrite in_fset_filter v_rem andbC negbK.
Qed.

Lemma conflicts_dis σ vs v :
  v \in supp σ -> v \notin conflicts σ vs ->
  fdisjoint (zexpr_vars [::] (σ v)) (conflicts σ vs).
Proof.
apply: (@loop_dis vs).
- by rewrite fsubset_leq_size // fsubDset fsubsetUr.
- exact: fsubsetxx.
- exact: fsubsetUr.
by move=> {}v v_σ; rewrite fsetDv fdisjoints0.
Qed.

End Conflicts.

Fixpoint inline_loop σ c : subst * com :=
  match c with
  | CSkip => (σ, CSkip)
  | CAssn assn c =>
    let assn := subst_assn σ assn in
    let det_assn := filter_map (fun=> of_dirac) assn in
    let cs := conflicts σ (domm assn) in
    let σ_def v := if v \in cs then ZSym v
                   else if det_assn v is Some e then e
                   else σ v in
    let σ := mkffun σ_def (domm det_assn :|: supp σ) in
    let: (σ, c) := inline_loop σ c in
    (σ, Assn assn;; c)
  | CIf e cthen celse c =>
    let e' := subst_bexpr (app_subst σ) e in
    let: (σ_then, cthen') := inline_loop σ cthen in
    let: (σ_else, celse') := inline_loop σ celse in
    let modified := com_mod_vars cthen' :|: com_mod_vars celse' in
    let can_merge := fdisjoint (bexpr_vars [::] e') modified in
    let σ_def v := if can_merge then ZTest e' (σ_then v) (σ_else v)
                   else if σ_then v == σ_else v then σ_then v
                   else ZSym v in
    let σ := mkffun σ_def (supp σ_then :|: supp σ_else) in
    let: (σ, c) := inline_loop σ c in
    (σ, CIf e' cthen' celse' c)
  | CBlock vs block c =>
    let cs := conflicts σ vs in
    let σ_def v := if v \in cs then ZSym v else σ v in
    let σ := mkffun σ_def (supp σ) in
    let: (σ, block) := inline_loop σ block in
    let cs := conflicts σ vs in
    let σ_def v := if v \in cs then ZSym v else σ v in
    let σ := mkffun σ_def (supp σ) in
    let: (σ, c) := inline_loop σ c in
    (σ, CBlock vs block c)
  end.

Definition wf_subst defs σ st :=
  forall v, feval_zexpr defs st (σ v) = st v.

Lemma wf_subst0 defs st : wf_subst defs emptyf st.
Proof. by move=> ?; rewrite emptyfE. Qed.

Lemma wf_subst_feval_zexpr σ st defs e :
  wf_subst defs σ st ->
  feval_zexpr defs st (subst_zexpr (app_subst σ) e) = feval_zexpr defs st e.
Proof.
move=> wf; rewrite /feval_zexpr subst_zexprP.
apply/eq_eval_zexpr; case=> [v|s] //=; exact: wf.
Qed.

Lemma wf_subst_feval_bexpr σ st defs e :
  wf_subst defs σ st ->
  feval_bexpr defs st (subst_bexpr (app_subst σ) e) = feval_bexpr defs st e.
Proof.
move=> wf; rewrite /feval_bexpr subst_bexprP.
apply/eq_eval_bexpr; case=> [v|s] //=; exact: wf.
Qed.

Definition inline_loop_spec c :=
  forall σ σ' c' st,
    wf_subst [::] σ st ->
    inline_loop σ c = (σ', c') ->
    let p := run [::] c st in
    run [::] c' st = p /\
    forall st', st' \in supp p -> wf_subst [::] σ' st'.

Lemma inline_loop_skip : inline_loop_spec CSkip.
Proof.
move=> σ _ _ st wf [<- <-]; split=> //= st'.
by move=> /supp_diracP -> .
Qed.

Lemma inline_loop_assn assn c :
  inline_loop_spec c ->
  inline_loop_spec (CAssn assn c).
Proof.
move=> IH σ σ'' c'' st /=.
set assn' := subst_assn σ assn.
set det_assn := filter_map _ _.
set cs := conflicts σ _.
set σ'_def := fun v => if v \in cs then ZSym v else _.
set σ' := mkffun _ _.
case ec: inline_loop => [{}σ'' {}c''] wf [<- <-] /=.
rewrite run_Assn /=.
have -> : do_assn [::] assn' st = do_assn [::] assn st.
  rewrite /do_assn /assn' /subst_assn mapm_p_comp /=.
  rewrite mapm_p_sample sampleA; apply/eq_sample=> /= vals.
  rewrite -mapm_p_comp mapm_p_dirac sample_diracL -mapm_comp.
  by under eq_mapm=> /= e do rewrite wf_subst_feval_zexpr //.
set p_st' := do_assn [::] assn st.
suff wf' st' : st' \in supp p_st' -> wf_subst [::] σ' st'.
  split.
    by apply/eq_in_sample=> st' {}/wf' wf'; case: (IH _ _ _ _ wf' ec).
  move=> st'' /supp_sampleP [st' {}/wf' wf'].
  case: (IH _ _ _ _ wf' ec)=> _; exact.
move=> st'P.
have st_cs v: v \notin cs -> st' v = st v.
  move=> v_cs; have: v \notin domm assn'.
    apply: contra v_cs; apply/fsubsetP/conflicts_sub.
  rewrite domm_map=> vP.
  case/supp_sampleP: st'P=> /= exps /supp_mapm_pP [ed _] /supp_diracP ->.
  rewrite updmE mapmE; move: vP; rewrite ed mem_domm.
  by case: (exps v).
move=> v; rewrite /σ' mkffunE; case: ifP=> // v_domm.
rewrite /σ'_def; case: ifPn=> // v_cs.
have /dommPn det_v: v \notin domm det_assn.
  apply: contra v_cs; apply/fsubsetP.
  apply: fsubset_trans (conflicts_sub _ _).
  by rewrite domm_filter_map fset_filter_subset.
rewrite in_fsetU mem_domm det_v /= in v_domm *.
have dis : fdisjoint (zexpr_vars [::] (σ v)) cs by exact: conflicts_dis.
rewrite st_cs // -wf; apply: eq_in_feval_zexpr => v' in_σ_v.
apply: st_cs; exact: (fdisjointP dis).
Qed.

Lemma inline_loop_if e cthen celse c :
  inline_loop_spec cthen ->
  inline_loop_spec celse ->
  inline_loop_spec c ->
  inline_loop_spec (CIf e cthen celse c).
Proof.
move=> IHthen IHelse IHc σ σ'' c' st /=.
case ethen: (inline_loop σ cthen)=> [σ_then cthen'].
case eelse: (inline_loop σ celse)=> [σ_else celse'].
set e' := subst_bexpr (app_subst σ) e.
set cond := feval_bexpr [::] st e.
set cb := if cond then cthen else celse.
set cb' := if cond then cthen' else celse'.
set can_merge := fdisjoint _ _.
set σ'_def := fun v => if can_merge then _ else _.
set σ' := mkffun σ'_def (supp σ_then :|: supp σ_else).
set σ_b := if cond then σ_then else σ_else.
have {IHthen IHelse} IHb : inline_loop_spec cb.
  rewrite /cb; case: (cond); [exact: IHthen|exact: IHelse].
have eb : inline_loop σ cb = (σ_b, cb').
  by rewrite /cb /σ_b /cb'; case: (cond).
case ec: (inline_loop σ' c)=> [{}σ'' {}c'] wf [<- <-] /=.
rewrite wf_subst_feval_bexpr // -/cond -/cb'.
case/(_ _ _ _ _ wf eb): IHb=> ecb wf'.
suff wf'' st' : st' \in supp (run [::] cb st) -> wf_subst [::] σ' st'.
  split.
    rewrite ecb; apply/eq_in_sample=> st' {}/wf'' wf''.
    by case/(_ _ _ _ _ wf'' ec): IHc.
  move=> st'' /supp_sampleP [st' {}/wf'' wf'' st''_supp].
  case/(_ _ _ _ _ wf'' ec): IHc=> _; exact.
move=> st'_supp v; move/(_ _ st'_supp v) in wf'.
rewrite -wf' /σ' mkffunE; case: ifPn=> [_|]; last first.
  rewrite in_fsetU negb_or; case/andP=> /suppPn v_then /suppPn v_else.
  by rewrite /σ_b; case: (cond); rewrite ?v_then ?v_else.
rewrite /σ'_def /σ_b /=; case: (boolP can_merge)=> [dis|_].
  have {}dis: fdisjoint (bexpr_vars [::] e') (com_mod_vars cb').
    move: dis; rewrite /can_merge fdisjointUr; case/andP.
    by rewrite /cb'; case: (cond).
  pose cond' := feval_bexpr [::] st' e'.
  pose ev e := feval_zexpr [::] st' e.
  rewrite -[LHS]/(if cond' then ev (σ_then v) else ev (σ_else v)).
  have ->: cond' = feval_bexpr [::] st e'.
    apply/eq_in_feval_bexpr=> v' /(fdisjointP dis).
    move: st'_supp; rewrite -ecb; exact: com_mod_varsP.
  by rewrite wf_subst_feval_bexpr // /cond; case: feval_bexpr.
case: eqP=> [?|_]; first by case: (cond)=> //; congruence.
by rewrite wf'.
Qed.

Lemma inline_loop_block vs block c :
  inline_loop_spec block ->
  inline_loop_spec c ->
  inline_loop_spec (CBlock vs block c).
Proof.
move=> IHblock IHc σ0 σ4 c' st0 wf0 /=.
set cs0 := conflicts σ0 vs.
set σ1_def := fun v => if v \in cs0 then ZSym v else σ0 v.
set σ1 := mkffun σ1_def (supp σ0).
case eblock: (inline_loop σ1 block)=> [σ2 block'].
set cs2 := conflicts σ2 vs.
set σ3_def := fun v => if v \in cs2 then ZSym v else σ2 v.
set σ3 := mkffun σ3_def (supp σ2).
case ec: (inline_loop σ3 c)=> [{}σ4 {}c'] [<- <-] /=.
set st1 := updm st0 (mkfmapf (fun=> 0%R) vs).
have wf1 : wf_subst [::] σ1 st1.
  move=> v; rewrite /σ1 /σ1_def mkffunE.
  case: ifPn=> //= v_σ0; case: ifPn=> //= v_cs0.
  have v_vs : v \notin vs.
    apply: contra v_cs0; apply/fsubsetP; exact: conflicts_sub.
  rewrite /st1 updmE mkfmapfE (negbTE v_vs).
  rewrite -wf0; apply/eq_in_feval_zexpr=> v' v'_v.
  rewrite updmE mkfmapfE.
  have v'_cs0 : v' \notin cs0.
    by move: v'_v; apply/fdisjointP; apply: conflicts_dis.
  suff /negbTE -> : v' \notin vs by [].
  apply: contra v'_cs0; apply/fsubsetP; exact: conflicts_sub.
have [{}eblock wf2] := IHblock _ _ _ _ wf1 eblock.
set r0 := mkfmapf st0 vs.
have r0E v : r0 v = if v \in vs then Some (st0 v) else None.
  by rewrite /r0 mkfmapfE; case: ifP=> // ->.
set p2 := run [::] block st1 in eblock *.
have wf3 st2 : st2 \in supp p2 -> wf_subst [::] σ3 (updm st2 r0).
  move=> {}/wf2 wf2 v; rewrite /σ3 /σ3_def mkffunE.
  case: ifP=> //= v_σ2; case: ifPn=> // v_cs2.
  have v_vs : v \notin vs.
    apply: contra v_cs2; apply/fsubsetP; exact: conflicts_sub.
  rewrite updmE r0E (negbTE v_vs) -wf2.
  apply/eq_in_feval_zexpr=> v' v'_v.
  have v'_cs2 : v' \notin cs2.
    by move: v'_v; apply/fdisjointP; apply: conflicts_dis.
  have v'_vs : v' \notin vs.
    apply: contra v'_cs2; apply/fsubsetP; exact: conflicts_sub.
  by rewrite updmE r0E (negbTE v'_vs).
rewrite !do_blockE /= eblock; split.
  apply/eq_in_sample=> st2 {}/wf3 wf3.
  by have [{}ec wf4] := IHc _ _ _ _ wf3 ec.
move=> st4 /supp_sampleP [st2 {}/wf3 wf3 st4_supp].
have [_ wf4] := IHc _ _ _ _ wf3 ec; exact: wf4.
Qed.

Lemma inline_loopP c : inline_loop_spec c.
Proof.
elim: c=> *.
- exact: inline_loop_skip.
- exact: inline_loop_assn.
- exact: inline_loop_if.
- exact: inline_loop_block.
Qed.

Definition inline c rew :=
  let: (σ, c') := inline_loop emptyf c in
  (c', [seq subst_zexpr (app_subst σ) e | e <- rew]).

Lemma inline_run c rew c' rew' st :
  inline c rew = (c', rew') ->
  run [::] c' st = run [::] c st.
Proof.
rewrite /inline; case e: (inline_loop emptyf _)=> [σ {}c'] [<- _].
by have [] := inline_loopP (wf_subst0 _ st) e.
Qed.

Lemma inline_rew c rew c' rew' st st' :
  inline c rew = (c', rew') ->
  st' \in supp (run [::] c st) ->
  [seq feval_zexpr [::] st' r | r <- rew'] =
  [seq feval_zexpr [::] st' r | r <- rew ].
Proof.
rewrite /inline; case e: (inline_loop emptyf _)=> [σ {}c'] [_ <-] in_supp.
have [_ /(_ _ in_supp) σP] := inline_loopP (wf_subst0 _ st) e.
rewrite -map_comp /=; apply/eq_map=> r /=.
exact: wf_subst_feval_zexpr.
Qed.

End Inlining.
