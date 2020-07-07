Require Import Coq.Strings.String.
Require Import Coq.Unicode.Utf8.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq
  ssrint rat ssralg ssrnum.

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
  (st : state) (defs : formulas) (v : var).

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
  sample: vals <- mapm_p id assn;
  dirac (updm st (mapm (feval_zexpr defs st) vals)).

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
    let old : state := mkffun st vs in
    let new := updm st (mkfmapf (fun _ => 0%R) vs) in
    sample: st' <- run defs block new;
    run defs c (updm st' (mkfmapf old vs))
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
apply/eq_ffun=> v; rewrite !updmE /= !mkfmapfE mkffunE.
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
  rewrite (IHc _ _ st''_supp v_c) updmE mkfmapfE mkffunE.
  case: (boolP (v \in vs)) v_mod=> //= v_vs v_block.
  by rewrite (IHblock _ _ st'_supp v_block) updmE mkfmapfE (negbTE v_vs).
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
set r0 := mkfmapf (mkffun st0 vs) vs.
have r0E v : r0 v = if v \in vs then Some (st0 v) else None.
  by rewrite /r0 mkfmapfE mkffunE; case: ifP=> // ->.
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

End Inlining.
