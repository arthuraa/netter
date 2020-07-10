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
  (st : state) (defs : formulas) (vs : {fset var}) (v : var).

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
  else if c is CSkip then CSkip
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
    let new := updm st (mkfmapf (fun _ => 0%R) vs) in
    sample: st' <- run defs block new;
    run defs c (updm st' (mkfmapf st vs))
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
  rewrite (_ : updm st _ = st).
    rewrite -[LHS]sample_diracR; apply/eq_sample=> /= st'.
    by congr dirac; apply/eq_ffun=> v; rewrite updmE /=.
  by apply/eq_ffun=> v /=; rewrite updmE /=.
case: c=> //=; rewrite sample_diracL; congr dirac.
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
- move=> vs c _ c' IH st; rewrite sampleA.
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

Lemma com_mod_varsP defs c st st' v :
  st' \in supp (run defs c st) ->
  v \notin com_mod_vars c ->
  st' v = st v.
Proof.
elim: c st st'.
- by move=> /= st st' /supp_diracP ->.
- move=> /= assn c IH st st''.
  case/supp_sampleP=> st' /do_assnP-/(_ v).
  rewrite in_fsetU negb_or mem_domm.
  by case assn_v: (assn v)=> //= <-; eauto.
- move=> /= e cthen IHthen celse IHelse c IH st st''.
  case/supp_sampleP=> st' st'_supp st''_supp.
  rewrite !in_fsetU !negb_or -andbA; case/and3P=> cthenP celseP cP.
  rewrite (IH _ _ st''_supp) //.
  by case: (feval_bexpr defs st e) st'_supp=> ?; eauto.
- move=> /= vs block IHblock c IHc st st''.
  case/supp_sampleP=> st' st'_supp st''_supp.
  rewrite in_fsetU in_fsetD negb_or; case/andP=> v_mod v_c.
  rewrite (IHc _ _ st''_supp v_c) updmE mkfmapfE.
  case: (boolP (v \in vs)) v_mod=> //= v_vs v_block.
  by rewrite (IHblock _ _ st'_supp v_block) updmE mkfmapfE (negbTE v_vs).
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

Definition dependencies := ffun (fun v : var => fset1 v).
Implicit Types deps : dependencies.

Definition lift_deps deps vs := \bigcup_(v <- vs) deps v.

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

Lemma assn_depsP2 defs assn1 assn2 vs :
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

Fixpoint com_deps defs c : dependencies :=
  match c with
  | CSkip => emptyf
  | CAssn assn c =>
    let deps_c := com_deps defs c in
    deps_comp (assn_deps defs assn) deps_c
  | CIf e cthen celse c =>
    let deps_then := com_deps defs cthen in
    let deps_else := com_deps defs celse in
    let ve := bexpr_vars defs e in
    let mod := com_mod_vars cthen :|: com_mod_vars celse in
    let deps_b_def v := ve :|: deps_then v :|: deps_else v in
    let deps_b := mkffun deps_b_def mod in
    deps_comp deps_b (com_deps defs c)
  | CBlock locals block c =>
    let deps_locals : dependencies := mkffun (fun=> fset0) locals in
    let deps_block := deps_comp deps_locals (com_deps defs block) in
    let deps_block' := mkffun deps_block (supp deps_block :\: locals) in
    let deps_c := com_deps defs c in
    deps_comp deps_block' deps_c
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
  set deps_locals := mkffun (fun=> fset0) locals.
  set deps_block := deps_comp deps_locals (com_deps defs block).
  set deps_block' := mkffun deps_block _.
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
  exact: assn_depsP2.
- move=> /= e cthen IHthen celse IHelse c IHc.
  apply: deps_compP=> // vs st1 st2.
  set deps_then := com_deps defs cthen.
  set deps_else := com_deps defs celse.
  set ve := bexpr_vars defs e.
  set mod := com_mod_vars cthen :|: com_mod_vars celse.
  set deps_b_def := fun v => ve :|: deps_then v :|: deps_else v.
  set deps_b := mkffun deps_b_def mod.
  set b1 := feval_bexpr defs st1 e.
  set b2 := feval_bexpr defs st2 e.
  have [dis|not_dis] := boolP (fdisjoint vs mod).
    rewrite /lift_deps big_seq; under eq_big=> [?|v v_vs]; first over.
      rewrite /deps_b mkffunE (negbTE (fdisjointP dis _ v_vs)); over.
    rewrite -big_seq bigcup1 fsvalK => R12.
    apply: coupling_trivial=> st1' st2' st1'P st2'P v v_vs.
    have v_mod := fdisjointP dis _ v_vs.
    have {}v_mod b : v \notin com_mod_vars (if b then cthen else celse).
      apply: contra v_mod; rewrite /mod in_fsetU.
      case: b=> -> //; exact: orbT.
    have -> : st1' v = st1 v by exact: com_mod_varsP st1'P (v_mod b1).
    have -> : st2' v = st2 v by exact: com_mod_varsP st2'P (v_mod b2).
    exact: R12.
  set vs' := \bigcup_(v <- vs) deps_b v.
  have sub : fsubset ve vs'.
    have [v v_vs v_mod] : exists2 v, v \in vs & v \in mod.
      by case/fset0Pn: not_dis=> v /fsetIP [] ??; exists v.
    have sub : fsubset ve (deps_b v).
      by rewrite /deps_b mkffunE v_mod /deps_b_def -fsetUA fsubsetUl.
    apply: fsubset_trans sub _.
    exact: bigcup_sup.
  move=> R12; have R12' : {in ve, st1 =1 st2}.
    by move=> v v_ve; apply: R12; apply/fsubsetP: v_ve.
  have -> : b1 = b2 by apply/eq_in_feval_bexpr.
  set cb := if b2 then cthen else celse.
  set deps_b' := if b2 then deps_then else deps_else.
  have IHcb : deps_spec deps_b' (run defs cb).
    by rewrite /deps_b' /cb; case: (b2).
  have sub_deps v : fsubset (deps_b' v) (deps_then v :|: deps_else v).
    by rewrite /deps_b'; case: (b2); rewrite ?fsubsetUr ?fsubsetUl.
  suff {}IHcb' : deps_spec deps_b (run defs cb) by apply: IHcb'.
  apply: deps_specW IHcb=> v1; apply: fsubset_trans (sub_deps v1) _.
  rewrite /deps_b mkffunE; case: ifPn=> [in_mod|nin_mod].
    by rewrite /deps_b_def -fsetUA fsubsetUr.
  move: nin_mod; rewrite in_fsetU; case/norP=> nin_then nin_else.
  have /suppPn -> : v1 \notin supp deps_then.
    by apply: contra nin_then; apply/fsubsetP/supp_com_deps.
  have /suppPn -> : v1 \notin supp deps_else.
    by apply: contra nin_else; apply/fsubsetP/supp_com_deps.
  by rewrite fsetUid fsubsetxx.
- move=> locals block IHblock c IHc /=.
  set reset := mkffun (fun=> fset0) locals.
  set deps_block0 := com_deps defs block in IHblock *.
  set deps_block1 := deps_comp reset deps_block0 in IHblock *.
  set deps_block2 := mkffun deps_block1 _.
  set deps_c := com_deps defs c in IHc *.
  set zeroed := mkfmapf (fun=> 0%R) locals.
  pose zero st := updm st zeroed.
  pose f st := sample: st' <- run defs block (zero st);
               dirac (updm st' (mkfmapf st locals)).
  suff compP : deps_spec (deps_comp deps_block2 deps_c)
                         (fun st => sample: st' <- f st; run defs c st').
    move=> st1 st2 vs R12; move: (compP _ _ _ R12); rewrite /f !sampleA.
    by do 2![under [in _ _ (fun _ => sample _ _)]eq_sample do rewrite sample_diracL].
  have deps_zero : deps_spec reset (dirac \o zero).
    move=> st1 st2 vs R12; apply: coupling_dirac => v v_vs.
    rewrite /zero !updmE mkfmapfE; case: ifP=> // v_locals.
    apply: R12; apply/bigcupP.
    by exists v; rewrite // mkffunE v_locals in_fset1.
  have IHblock1 := deps_compP deps_zero IHblock.
  rewrite -/deps_block1 in IHblock1.
  apply: deps_compP IHc => vs st1 st2 R12; rewrite /f.
  have /IHblock1 R12': {in lift_deps deps_block1 (vs :\: locals), st1 =1 st2}.
    move=> v /bigcupP [] v' /fsetDP [v'_vs v'_locals] _ v_v'; apply: R12.
    apply/bigcupP; exists v'; rewrite // mkffunE.
    case: ifPn=> //; rewrite in_fsetD negb_and negbK.
    by rewrite (negbTE v'_locals) => /suppPn <-.
  rewrite /= !sample_diracL in R12'; apply: coupling_sample R12' _.
  move=> st1' st2' _ _ R12'; apply: coupling_dirac => v v_vs.
  rewrite !updmE !mkfmapfE; case: ifPn=> v_locals; last first.
    by apply: R12'; apply/fsetDP.
  apply: R12; apply/bigcupP; exists v; rewrite // mkffunE.
  by rewrite in_fsetD v_locals in_fset1.
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

Fixpoint dead_store_elim defs c live :=
  match c with
  | CSkip => CSkip
  | CAssn assn c =>
    let live' := lift_deps (com_deps defs c) live      in
    let assn' := filterm (fun v _ => v \in live') assn in
    let c'    := dead_store_elim defs c live           in
    CAssn assn' c'
  | CIf e cthen celse c =>
    let live'  := lift_deps (com_deps defs c) live in
    let cthen' := dead_store_elim defs cthen live' in
    let celse' := dead_store_elim defs celse live' in
    let c'     := dead_store_elim defs c live      in
    CIf e cthen' celse' c'
  | CBlock locals block c =>
    let live'  := lift_deps (com_deps defs c) live  in
    let live'' := live' :\: locals                  in
    let block' := dead_store_elim defs block live'' in
    let c'     := dead_store_elim defs c live       in
    CBlock locals block' c'
  end.

Lemma dead_store_elimP defs c live st1 st2 :
  let deps := com_deps defs c in
  let R vs st1 st2 := {in vs, st1 =1 st2} in
  let c' := dead_store_elim defs c live in
  R (lift_deps deps live) st1 st2 ->
  coupling (R live) (run defs c st1) (run defs c' st2).
Proof. Admitted.

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
rewrite eblock; split.
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
