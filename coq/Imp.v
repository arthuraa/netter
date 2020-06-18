Require Import Coq.Strings.String.
Require Import Coq.Unicode.Utf8.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq
  ssrint rat ssralg ssrnum.

From extructures Require Import ord fset fmap.

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
(* /MOVE *)

Inductive com :=
| Skip
| Assn of {fmap var -> {prob zexpr}} & com
| If of bexpr & com & com & com
| Block of {fset var} & com & com.

Record state :=
  State {stval : {fmap var -> {x : int | x != 0}}}.

Canonical state_newType := [newType for stval].
Definition state_eqMixin := [eqMixin of state by <:].
Canonical state_eqType := EqType state state_eqMixin.
Definition state_choiceMixin := [choiceMixin of state by <:].
Canonical state_choiceType := Eval hnf in ChoiceType state state_choiceMixin.
Definition state_ordMixin := [ordMixin of state by <:].
Canonical state_ordType := Eval hnf in OrdType state state_ordMixin.

Definition fun_of_state (st : state) (v : var) : int :=
  if val st v is Some n then val n else 0.

Coercion fun_of_state : state >-> Funclass.

Implicit Types (c : com) (st : state) (φ : state → var → int).

Lemma eq_state st1 st2 : st1 =1 st2 <-> st1 = st2.
Proof.
split=> [e|-> //]; apply/val_inj.
apply/eq_fmap=> v; move: (e v).
rewrite /fun_of_state.
case: (val st1 v) (val st2 v)=> [y1|] [y2|] //=.
- by move=> /val_inj ->.
- by move=> {}e; move: (valP y1); rewrite /=  e.
- by move=> {}e; move: (valP y2); rewrite /= -e.
Qed.

Definition state_of_fun (X : {fset var}) (f : var -> int) :=
  State (mkfmapfp (insub \o f) X).

Lemma state_of_funE X f x :
  state_of_fun X f x = if x \in X then f x else 0.
Proof.
rewrite /state_of_fun /fun_of_state /= mkfmapfpE /=.
case: (x \in X)=> //.
case: insubP=> [? ? -> //|].
by rewrite negbK=> /eqP ->.
Qed.

Definition upd st (assn : {fmap var -> int}) : state :=
  state_of_fun (domm (val st) :|: domm assn)
    (fun v => if assn v is Some x then x else st v).

Lemma updE st assn v :
  upd st assn v = if assn v is Some x then x else st v.
Proof.
rewrite /upd state_of_funE in_fsetU /fun_of_state /= !mem_domm.
case: (stval st v)=> //=.
by case: (assn v).
Qed.

Fixpoint run φ c st : {prob state} :=
  match c with
  | Skip =>
    dirac st
  | Assn assn c =>
    let eval _ pe := sample: e <- pe; dirac (eval_zexpr (φ st) e) in
    sample: assn' <- mapim_p eval assn;
    run φ c (upd st assn')
  | If e cthen celse c =>
    let branch := if eval_bexpr (φ st) e then cthen else celse in
    sample (run φ branch st) (run φ c)
  | Block vs block c =>
    let old := state_of_fun vs st in
    let new := upd st (mkfmapf (fun _ => 0%R) vs) in
    sample: st' <- run φ block new;
    run φ c (upd st' (mkfmapf old vs))
  end.

Record renaming := Renaming {
  ren_val : {fmap var → var};
  _       : all (fun v => ren_val v != Some v) (domm ren_val);
}.

Canonical renaming_subType := [subType for ren_val].

Definition fun_of_renaming (r : renaming) v :=
  if val r v is Some v' then v' else v.

Coercion fun_of_renaming : renaming >-> Funclass.

Module Inlining.

Definition fresh_for (fv : {fmap string → nat}) (V : {fset var}) :=
  ∀ x n, Var x n \in V → if fv x is Some m then n <= m else false.

Record istate := IState {
  fresh_vars  : {fmap string → nat};
  formulas    : seq (var * zexpr);
  used_vars   : {fmap var → {fset var}};
  ren         : renaming;
}.

Definition M T : Type := istate → istate * T.

Definition ret T (x : T) : M T :=
  fun s => (s, x).

Definition bind T S (x : M T) (f : T → M S) : M S :=
  fun s => f (x s).2 (x s).1.

Notation "'bind:' x '<-' t1 ';' t2" :=
  (bind t1 (fun x => t2))
  (at level 20, t1 at level 100, t2 at level 200,
   right associativity, format "'[' 'bind:'  x  '<-'  '[' t1 ;  ']' ']' '/' t2 ").

Definition get T (f : istate → T) : M T :=
  fun s => (s, f s).

Definition mod (f : istate → istate) : M unit :=
  fun s => (f s, tt).

Definition set_fresh_vars fv : M unit :=
  mod (fun '(IState _ f u r) => IState fv f u r).

Definition fresh (x : string) : M var :=
  bind: fv <- get fresh_vars;
  if fv x is Some m then
    bind: _ <- set_fresh_vars (setm fv x m.+1);
    ret (Var x m)
  else
    bind: _ <- set_fresh_vars (setm fv x 0);
    ret (Var x 0).

Definition intern_var (v : var) (e : zexpr) : M unit :=
  bind: v' <- fresh (vname v);
  bind: u  <- get used_vars;
  let vs := \bigcup_(v'' <- zexpr_vars e) u v'' in
  mod (fun '(IState fv fs uv r) => IState fv ((v', e) :: fs)

Fixpoint inline_loop (c : com) : M com :=
  match c with
  | Skip =>
    ret Skip
  | Assn assn c =>
    let det_assn := filter_map (fun=> of_dirac) assn in
    if domm det_assn == domm assn then
      bind: r <- get renaming;
      let det_assn := mapm (subst_zexpr (ZVar \o r)) det_assn in



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
