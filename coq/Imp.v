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

Module Inlining.

Module Type CONFLICTS.
Parameter conflicts :
  renaming -> {fset var} -> {fset var}.
Parameter conflicts_sub :
  forall rn vs, fsubset vs (conflicts rn vs).
Parameter conflicts_dis :
  forall rn vs v,
  v \in supp rn -> v \notin conflicts rn vs ->
  fdisjoint (zexpr_vars (rn v)) (conflicts rn vs).
End CONFLICTS.

Module Export Conflicts : CONFLICTS.

Definition conflicts rn vs := supp rn :|: vs.

Lemma conflicts_sub rn vs : fsubset vs (conflicts rn vs).
Proof. exact: fsubsetUr. Qed.

Lemma conflicts_dis rn vs v :
  v \in supp rn -> v \notin conflicts rn vs ->
  fdisjoint (zexpr_vars (rn v)) (conflicts rn vs).
Proof. by rewrite /conflicts in_fsetU => ->. Qed.

End Conflicts.

Inductive checkpoint_spec rn vs : renaming * renaming -> Prop :=
| CheckpointSpec rn1 rn2 of
  (forall st, flush id st (val rn) =
    flush id (flush id st (val rn1)) (val rn2)) &
  fdisjoint (supp rn2) vs &
  (forall v, v \in supp rn2 -> fdisjoint (zexpr_vars (rn2 v)) vs)
  : checkpoint_spec rn vs (rn1, rn2).

Module Type CHECKPOINT.
Parameter checkpoint :
  renaming -> {fset var} -> renaming * renaming.
Parameter checkpointP :
  forall rn vs, checkpoint_spec rn vs (checkpoint rn vs).
End CHECKPOINT.

Module Export Checkpoint : CHECKPOINT.

Definition checkpoint rn vs : renaming * renaming :=
  let flush := conflicts rn vs in
  let rn1   := mkffun rn flush in
  let rn2   := mkffun rn (supp rn :\: flush) in
  (rn1, rn2).

Lemma checkpointP rn vs : checkpoint_spec rn vs (checkpoint rn vs).
Proof.
exists.
- move=> st; apply/eq_ffun=> /= v; rewrite !flushER mkffunE.
  rewrite in_fsetD; case: (boolP (v \in conflicts rn vs))=> vc /=.
    by rewrite flushER mkffunE vc.
  case: ifPn=> vrn /= .
    apply/(@eq_in_eval_zexprP (zexpr_vars (rn v))); rewrite ?fsubsetxx //.
    move=> v' v'v; rewrite flushER mkffunE.
    by move: (fdisjointP (conflicts_dis vrn vc) _ v'v)=> /negbTE ->.
  by rewrite flushER mkffunE (negbTE vc) (suppPn vrn).
- apply/fdisjointP=> v; rewrite mem_supp mkffunE in_fsetD.
  case: (boolP (v \in conflicts rn vs)); rewrite /= ?eqxx //.
  move=> vc _; apply: contra vc.
  exact: (fsubsetP (conflicts_sub rn vs)).
- move=> v; rewrite mem_supp mkffunE in_fsetD.
  case: ifP; rewrite ?eqxx //.
  case/andP=> vc vrn e; apply/fdisjointP=> v' v'v.
  have {}v'v: v' \notin conflicts rn vs.
    exact: (fdisjointP (conflicts_dis vrn vc)).
  apply: contra v'v; exact: (fsubsetP (conflicts_sub rn vs)).
Qed.

End Checkpoint.

Fixpoint inline_loop rn c : renaming * com :=
  match c with
  | CSkip => (rn, CSkip)
  | CAssn assn c =>
    let det_assn := filter_map (fun=> of_dirac) assn in
    if domm det_assn == domm assn then
      let assn' := mapm (subst_zexpr rn) det_assn in
      let rn'   := updm rn assn' in
      inline_loop rn' c
    else
      let: (rn0, rn1) := checkpoint rn (domm assn) in
      let: (rn2, c') :=  inline_loop rn1 c in
      let  assn' := mapm (subst_zexpr rn1) assn in
      (rn2, DAssn (val rn0);; Assn assn';; c')
  | CIf e cthen celse c =>
    let e' := subst_bexpr rn e in
    let: (rn_then, cthen') := inline_loop rn cthen in
    let: (rn_else, celse') := inline_loop rn celse in
    let to_flush0 := supp rn_then :|: supp rn_else in
    let updated v := (rn_then v != rn v) || (rn_else v != rn v) in
    let to_flush1 := fset_filter updated to_flush0 in
    if (cthen' == CSkip) && (celse' == CSkip) then
      let merge v := ZTest e' (rn_then v) (rn_else v) in
      let assn' := mkfmapf merge to_flush1 in
      let rn' := updm rn assn' in
      inline_loop rn' c
    else
      let assn_then := mkfmapf (dirac \o rn_then) to_flush1 in
      let cthen''   := Seq cthen' (CAssn assn_then CSkip) in
      let assn_else := mkfmapf (dirac \o rn_else) to_flush1 in
      let celse''   := Seq celse' (CAssn assn_else CSkip) in
      let rn_merge  := updm rn (mkfmapf ZVar to_flush1) in
      let: (rn', c') := inline_loop rn_merge c in
      (rn', CIf e' cthen'' celse'' c')
  | CBlock vs block c =>
    let: (rn0, rn1) := checkpoint rn vs in
    let: (rn_block, block') := inline_loop rn1 block in
    let: (rn2, rn3) := checkpoint rn_block vs in
    let: (rn4, c') := inline_loop rn1 c in
    (rn2, DAssn (val rn0);; Block vs (block';; DAssn (val rn2));; c')
  end.

Lemma inline_loopP rn c rn' c' st :
  inline_loop rn c = (rn', c') ->
  run id (DAssn (val rn);; c) st =
  run id (c';; DAssn (val rn')) st.
Proof.
elim: c rn c' rn' st.
- by move=> rn _ _ st [<- <-] /=; rewrite Seqc1.
- move=> assn c IH rn c' rn' st /=.
  case: (altP (domm _ =P domm _))=> [e|_].
  + set assn' := filter_map (fun=> of_dirac) assn in e.
    have assnE : assn = mapm dirac assn'.
      apply/eq_fmap=> v; move/eq_fset/(_ v): e.
      rewrite !mem_domm /assn' mapmE filter_mapE.
      case: (assn v)=> [pe|] //=.
      by case: (of_dirac pe) (of_diracK pe)=> //= e ->.
    move: assn' e assnE=> /= {}assn _ ->.
    rewrite mapimK; last by move=> _; exact: diracK.
    set rn0 := updm rn _; move=> {}/IH <-.
    rewrite !run_DAssn -run_Assn run_DAssn; congr run.
    apply/eq_ffun=> /= v.
    rewrite !flushER flushE flushER /rn0 updmE mapmE.
    case: (assn v)=> //= e.
    by rewrite subst_zexprP; apply/eq_eval_zexpr=> v'; rewrite flushER.
  + case: checkpointP=> rn0 rn1 chk1 chk2 chk3.
    case e: (inline_loop rn1 c)=> [{}rn' {}c'] [<- <-].
    move/IH in e.
    rewrite run_DAssn -run_Assn chk1 -run_DAssn. -![in RHS]SeqA [RHS]run_DAssn.
    rewrite -


Lemma inline_loopP rn c st :
  let res := inline_loop rn c in
  run id c (flush st rn) =
  sample: st' <- run id res.2 st;
  dirac (flush st' res.1).
Proof.
elim: c rn st.
- by move=> rn st; rewrite /= sample_diracL.
- move=> assn c IH rn st /=.
  case: (altP (domm _ =P domm _))=> [e|_].
  + set assn' := filter_map (fun=> of_dirac) assn in e.
    have assnE : assn = mapm dirac assn'.
      apply/eq_fmap=> v; move/eq_fset/(_ v): e.
      rewrite !mem_domm /assn' mapmE filter_mapE.
      case: (assn v)=> [pe|] //=.
      by case: (of_dirac pe) (of_diracK pe)=> //= e ->.
    move: assn' e assnE=> /= {}assn _ ->.
    rewrite mapm_p_comp.
    under eq_mapm_p => ? do rewrite /= sample_diracL.
    rewrite -(mapm_p_comp dirac (eval_zexpr (flush st rn))).
    rewrite mapm_p_dirac sample_diracL mapimK; last first.
      move=> _; exact: diracK.
    by rewrite updm_flush IH.
  + case: checkpointP=> rn0 rn1 chk1 chk2 chk3.
    rewrite [inline_loop rn1 c]surjective_pairing /=.
    rewrite -SeqA run_Seq assn_of_rnP sample_diracL.



    rewrite -mapm_mkfmapf mapm_p_comp.
    under [in RHS]eq_mapm_p => /= e do rewrite sample_diracL.
    set to_flush := conflicts rn (domm assn).
    set assn0 := mkfmapf rn to_flush.
    rewrite -[in RHS]mapm_p_comp mapm_p_dirac sample_diracL /= sampleA.
    set rn0 := updm rn (mkfmapf ZVar to_flush).
    set st0 := updm st (mapm (eval_zexpr st) assn0).
    rewrite mapm_p_comp /=.
    under [in RHS]eq_mapm_p => pe.
      rewrite /= sampleA.
      under eq_sample => e.
        rewrite sample_diracL subst_zexprP.
        under eq_eval_zexpr=> v.
          rewrite (_ : eval_zexpr st0 (rn0 v) = flush st rn v); first over.
          rewrite flushE /rn0 updmE mkfmapfE.
          case: (boolP (v \in to_flush))=> [flush_v|not_flush_v].
            by rewrite /= /st0 updmE mapmE /assn0 mkfmapfE flush_v /=.


      over.
    under [in RHS]eq_mapm_p => pe.
      under eq_sample => e.


Module Inlining.

Notation renaming  := (ffun (fun v : var => v)).

Record istate := IState {
  fresh_vars  : ffun (fun n : string => 0 : nat);
  formulas    : seq (var * zexpr);
  (* Map formulas to the state variables needed to compute them. *)
  used_vars   : ffun (fun v : var => fset1 v);
}.

Implicit Types (rn : renaming) (ist : istate).

Definition state_view st rn ist :=
  updm st (mkfmapf (eval_forms (formulas ist) st \o rn) (supp rn)).

Definition istate_vars ist :=
  \bigcup_(p <- formulas ist) (fset1 p.1 :|: zexpr_vars p.2) :|:
  \bigcup_(v <- supp (used_vars ist)) used_vars ist v.

Definition wf_istate ist :=
  all (fun v => vnum v < fresh_vars ist (vname v)) (istate_vars ist).

Definition M T : Type := istate → istate * T.

Definition ret T (x : T) : M T :=
  fun s => (s, x).

Definition bind T S (x : M T) (f : T → M S) : M S :=
  fun s => f (x s).2 (x s).1.

Notation "'bind:' x '<-' t1 ';' t2" :=
  (bind t1 (fun x => t2))
  (at level 20, x pattern, t1 at level 100, t2 at level 200,
   right associativity, format "'[' 'bind:'  x  '<-'  '[' t1 ;  ']' ']' '/' t2").

Notation "f >> g" :=
  (bind f (fun _ => g))
  (at level 40, left associativity).

Definition get T (f : istate → T) : M T :=
  fun ist => (ist, f ist).

Definition mod (f : istate → istate) : M unit :=
  fun ist => (f ist, tt).

Definition intern1 (rn : renaming) (v : var) (e : zexpr) : M renaming := fun ist =>
  let: IState fv fs uv := ist in
  let n   := vname v in
  let vn  := fv n in
  let v'  := Var n vn in
  let fv' := upd fv n vn.+1 in
  let e'  := subst_zexpr (ZVar \o rn) e in
  let fs' := (v', e') :: fs in
  let vs  := \bigcup_(v'' <- zexpr_vars e) uv v'' in
  let uv' := upd uv v' vs in
  let rn' := upd rn v v' in
  (IState fv' fs' uv', rn').

Lemma intern1P rn v e ist ist' rn' st v' :
  intern1 rn v e ist = (ist', rn') ->
  eval_forms (formulas ist') st (rn' v') =
  if v' == v then
    eval_zexpr (eval_forms (formulas ist') st) e
  else eval_forms (formulas ist') st (rn v).
Proof.
case: ist=> fv fs uv /= [<- <-] {ist' rn'} /=.
rewrite updE; case: (altP (v' =P v))=> [_|ne].
  rewrite eqxx subst_zexprP; apply: eq_eval_zexpr=> v'' /=.

Definition intern (rn : renaming) (assn : {fmap var -> zexpr}) : M renaming :=
  foldl (fun f ve => bind: rn' <- f; intern1 rn' ve.1 ve.2) (ret rn) (val assn).

Definition conflicts (rn : renaming) (vs : {fset var}) : M {fset var} := fun ist =>
  let: IState fv fs uv := ist in
  (IState fv fs uv,
   fset_filter (fun v => fdisjoint (uv (rn v)) vs) (supp rn)).

Fixpoint inline_loop (rn : renaming) (c : com) : M (renaming * com) :=
  match c with
  | CSkip =>
    ret (rn, CSkip)
  | CAssn assn c =>
    let det_assn := filter_map (fun=> of_dirac) assn in
    if domm det_assn == domm assn then
      bind: rn' <- intern rn det_assn;
      inline_loop rn' c
    else
      bind: to_flush <- conflicts rn (domm assn);
      let assn0 := mkfmapf (dirac \o ZVar \o rn) to_flush in
      let rn0   := updm rn (mkfmapf id to_flush) in
      let assn1 := mapm (fun pe => sample: e <- pe; dirac (subst_zexpr (ZVar \o rn0) e)) assn in
      let rn1   := updm rn0 (mkfmapf id (domm assn1)) in
      bind: (rn', c') <- inline_loop rn c;
      ret (rn', CAssn assn0 (CAssn assn1 c'))
  | CIf e cthen celse c =>
    let e' := subst_bexpr (ZVar \o rn) e in
    bind: (rn_then, cthen') <- inline_loop rn cthen;
    bind: (rn_else, celse') <- inline_loop rn celse;
    let to_flush0 := supp rn_then :|: supp rn_else in
    let updated v := (rn_then v != rn v) || (rn_else v != rn v) in
    let to_flush1 := fset_filter updated to_flush0 in
    match cthen', celse' with
    | CSkip, CSkip =>
      let merge v := ZTest e' (ZVar (rn_then v)) (ZVar (rn_else v)) in
      bind: rn' <- intern rn (mkfmapf merge to_flush1);
      inline_loop rn' c
    | _, _ =>
      let assn_then := mkfmapf (dirac \o ZVar \o rn_then) to_flush1 in
      let cthen''   := Seq cthen' (CAssn assn_then CSkip) in
      let assn_else := mkfmapf (dirac \o ZVar \o rn_else) to_flush1 in
      let celse''   := Seq celse' (CAssn assn_else CSkip) in
      let rn_merge  := updm rn (mkfmapf id to_flush1) in
      bind: (rn', c') <- inline_loop rn_merge c;
      ret (rn', CIf e' cthen'' celse'' c')
    end
  | CBlock vs c1 c2 =>
    bind: to_flush0 <- conflicts rn vs;
    let assn0 := mkfmapf (dirac \o ZVar \o rn) to_flush0 in
    let rn0 := updm rn (mkfmapf id (to_flush0 :|: vs)) in
    bind: (rn1, c1') <- inline_loop rn0 c1;
    bind: to_flush1  <- conflicts rn1 vs;
    let assn1 := mkfmapf (dirac \o ZVar \o rn1) to_flush1 in
    let rn1'  := updm rn1 (mkfmapf id to_flush1) in
    bind: (rn2, c2') <- inline_loop rn1' c2;
    ret (rn2, CAssn assn0 (CBlock vs c1 c2))
  end.

Lemma inline_loopP rn rn' c c' ist ist' st :
  inline_loop rn c ist = (ist', (rn', c')) ->
  run id c (state_view st rn ist') =
  sample: st' <- run (eval_forms (formulas ist')) c' st;
  dirac (state_view st' rn' ist).
Proof.
elim: c rn rn' c' ist ist' st.
- move=> /= rn _ _ ist _ st [<- <- <-] /=.
  by rewrite sample_diracL.
- move=> /= assn c IH rn rn' c' ist ist' st.
  set det_assn := filter_map _ _; case: ifP=> [/eqP edomm|_].
  +

Definition spec T (P : istate → Prop) (x : M T) (Q : T → istate → Prop) : Prop :=
  ∀ s, P s → Q (x s).2 (x s).1.









Fixpoint com_read_vars c : {fset var} :=
  match c with
  | Skip =>
    fset0
  | Assn assn c =>
    assn_vars assn :|: com_read_vars c
  | If be cthen celse c =>
    bexpr_vars be :|:
    com_read_vars cthen :|:
    com_read_vars celse :|:
    com_read_vars c
  | Block vs block c =>
    (com_read_vars block :\: vs) :|:
    com_read_vars c
  end.

Lemma com_read_varsP (V : {fset var}) c st1 st2 :
  {in V, st1 =1 st2} ->
  fsubset (com_read_vars c) V ->
  forall st1', st1' \in supp (run c st1) ->
  forall st2', st2' \in supp (run c st2) ->
  {in V, st1' =1 st2'}.
Proof.
elim: c st1 st2=> //=.
- by move=> ??? _ _ /supp_diracP -> _ /supp_diracP ->.
- move=> assn c IH st1 st2 e.
  rewrite fsubUset; case/andP=> sub_c sub_assn.
  move=> st1' /supp_sampleP [/= vals1 vals1P st1'P].
  move=> st2' /supp_sampleP [/= vals2 vals2P st2'P].
  have {}e: {in V, upd st1 vals1 =1 upd st2 vals2}.
    admit.
  by apply: IH; eauto.
- move=> be cthen IHthen celse IHelse c IH st1 st2 e.
  rewrite !fsubUset -!andbA; case/and4P=> sub_be sub_cthen sub_celse sub_c.
  move=> st1'' /supp_sampleP [/= st1' st1'P st1''P].
  move=> st2'' /supp_sampleP [/= st2' st2'P st2''P].
  rewrite -(bexpr_varsP e sub_be) in st2'P.
  suff ?: {in V, st1' =1 st2'} by eauto using IH.
  case: eval_bexpr in st1'P st2'P.
  + by eauto using IHthen.
  + by eauto using IHelse.
