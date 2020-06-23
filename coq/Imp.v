Require Import Coq.Strings.String.
Require Import Coq.Unicode.Utf8.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq
  ssrint rat ssralg ssrnum.

From extructures Require Import ord fset fmap ffun.

From void Require Import void.

From deriving Require Import deriving.

From RandC Require Import Expr Prob.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.
Local Open Scope prob_scope.

(* MOVE *)
Section FilterMap.

Variables T : ordType.
Variables S R : Type.

Definition filter_map (f : T -> S -> option R) (m : {fmap T -> S}) : {fmap T -> R} :=
  mkfmapfp (fun x => obind (f x) (m x)) (domm m).

Lemma filter_mapE f m x : filter_map f m x = obind (f x) (m x).
Proof.
by rewrite /filter_map mkfmapfpE mem_domm; case: (m x).
Qed.
End FilterMap.

Section Update.

Context {T : ordType} {S : eqType} {def : T -> S}.

Definition updm (f : ffun def) (xs : {fmap T -> S}) : ffun def :=
  mkffun (fun v => if xs v is Some x then x else f v)
         (supp f :|: domm xs).

Lemma updmE f xs x :
  updm f xs x = if xs x is Some y then y else f x.
Proof.
rewrite /updm mkffunE in_fsetU orbC mem_domm.
case e: (xs x)=> [y|] //=.
by case: ifPn=> // /suppPn ->.
Qed.

End Update.
(* /MOVE *)

Inductive com :=
| CSkip
| CAssn of {fmap var -> {prob zexpr}} & com
| CIf of bexpr & com & com & com
| CBlock of {fset var} & com & com.

Definition com_indMixin := [indMixin for com_rect].
Canonical com_indType := IndType _ com com_indMixin.
Definition com_eqMixin := [derive eqMixin for com].
Canonical com_eqType := EqType com com_eqMixin.

Local Notation state := (ffun (fun x : var => 0 : int)).

Implicit Types (c : com) (st : state) (φ : state → var → int).

Definition Assn assn :=
  if assn == emptym then CSkip
  else CAssn assn CSkip.

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

Fixpoint run φ c st : {prob state} :=
  match c with
  | CSkip =>
    dirac st
  | CAssn assn c =>
    let eval _ pe := sample: e <- pe; dirac (eval_zexpr (φ st) e) in
    sample: assn' <- mapim_p eval assn;
    run φ c (updm st assn')
  | CIf e cthen celse c =>
    let branch := if eval_bexpr (φ st) e then cthen else celse in
    sample (run φ branch st) (run φ c)
  | CBlock vs block c =>
    let old : state := mkffun st vs in
    let new := updm st (mkfmapf (fun _ => 0%R) vs) in
    sample: st' <- run φ block new;
    run φ c (updm st' (mkfmapf old vs))
  end.

Lemma run_Assn φ assn st :
  run φ (Assn assn) st = run φ (CAssn assn CSkip) st.
Proof.
rewrite /Assn /=; case: eqP=> [->|] //=.
rewrite /mapim_p /= !sample_diracL; congr dirac.
by apply/eq_ffun=> v; rewrite updmE.
Qed.

Lemma run_Block φ vs c st :
  run φ (Block vs c) st = run φ (CBlock vs c CSkip) st.
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

Lemma run_Seq φ c1 c2 st :
  run φ (Seq c1 c2) st =
  sample: st' <- run φ c1 st; run φ c2 st'.
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

Module Inlining.

Notation renaming  := (ffun (fun v : var => v)).

Record istate := IState {
  fresh_vars  : ffun (fun n : string => 0 : nat);
  formulas    : seq (var * zexpr);
  (* Map formulas to the state variables needed to compute them. *)
  used_vars   : ffun (fun v : var => fset1 v);
}.

Fixpoint eval_forms (fs : seq (var * zexpr)) st v : int :=
  if fs is (f, e) :: fs then
    if v == f then eval_zexpr (eval_forms fs st) e
    else eval_forms fs st v
  else st v.

Implicit Types (ist : istate).

Definition M T : Type := istate → istate * T.

Definition ret T (x : T) : M T :=
  fun s => (s, x).

Definition bind T S (x : M T) (f : T → M S) : M S :=
  fun s => f (x s).2 (x s).1.

Notation "'bind:' x '<-' t1 ';' t2" :=
  (bind t1 (fun x => t2))
  (at level 20, x pattern, t1 at level 100, t2 at level 200,
   right associativity, format "'[' 'bind:'  x  '<-'  '[' t1 ;  ']' ']' '/' t2 ").

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

Definition intern (rn : renaming) (assn : {fmap var -> zexpr}) : M renaming :=
  foldl (fun f ve => bind: rn' <- f; intern1 rn' ve.1 ve.2) (ret rn) (val assn).

Definition conflicts (rn : renaming) (vs : {fset var}) : M {fset var} := fun ist =>
  let: IState fv fs uv := ist in
  (IState fv fs uv,
   fset_filter (fun v => fdisjoint (uv (rn v)) vs) (supp rn)).

Fixpoint inline_loop (rn : renaming) (c : com) : M (renaming * com) :=
  match c with
  | Skip =>
    ret (rn, Skip)
  | Assn assn c =>
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
      ret (rn', Assn assn0 (Assn assn1 c'))
  | If e cthen celse c =>
    let e' := subst_bexpr (ZVar \o rn) e in
    bind: (rn_then, cthen') <- inline_loop rn cthen;
    bind: (rn_else, celse') <- inline_loop rn celse;
    let to_flush0 := supp rn_then :|: supp rn_else in
    let updated v := (rn_then v != rn v) || (rn_else v != rn v) in
    let to_flush1 := fset_filter updated to_flush0 in
    match cthen', celse' with
    | Skip, Skip =>
      let merge v := ZTest e' (ZVar (rn_then v)) (ZVar (rn_else v)) in
      bind: rn' <- intern rn (mkfmapf merge to_flush1);
      inline_loop rn' c
    | _, _ =>
      let assn_then := mkfmapf (dirac \o ZVar \o rn_then) to_flush1 in
      let cthen''   := Seq cthen' (Assn assn_then Skip) in
      let assn_else := mkfmapf (dirac \o ZVar \o rn_else) to_flush1 in
      let celse''   := Seq celse' (Assn assn_else Skip) in
      let rn_merge  := updm rn (mkfmapf id to_flush1) in
      bind: (rn', c') <- inline_loop rn_merge c;
      ret (rn', If e' cthen'' celse'' c')
    end
  | Block vs c1 c2 =>
    bind: to_flush0 <- conflicts rn vs;
    let assn0 := mkfmapf (dirac \o ZVar \o rn) to_flush0 in
    let rn0 := updm rn (mkfmapf id (to_flush0 :|: vs)) in
    bind: (rn1, c1') <- inline_loop rn0 c1;
    bind: to_flush1  <- conflicts rn1 vs;
    let assn1 := mkfmapf (dirac \o ZVar \o rn1) to_flush1 in
    let rn1'  := updm rn1 (mkfmapf id to_flush1) in
    bind: (rn2, c2') <- inline_loop rn1' c2;
    ret (rn2, Assn assn0 (Block vs c1 c2))
  end.

Lemma inline_loopP rn c st :
  inline_loop rn c = (rn', c') ->
  run (eval_forms f) c (updm st (mkfmapf (eval_forms f \o rn) (supp rn))) =
  sample:

Definition spec T (P : istate → Prop) (x : M T) (Q : T → istate → Prop) : Prop :=
  ∀ s, P s → Q (x s).2 (x s).1.









Fixpoint com_read_vars c : {fset var} :=
  match c with
  | Skip =>
    fset0
  | Assn assn c =>
    com_read_vars c :|:
    \bigcup_(pe <- codomm assn)
    \bigcup_(e  <- supp pe) zexpr_vars e
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
