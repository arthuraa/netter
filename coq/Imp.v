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

Inductive com :=
| Skip
| Assn of {fmap var -> zexpr} & com
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

Implicit Types (c : com) (st : state).

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

Fixpoint run c st : {prob state} :=
  match c with
  | Skip =>
    dirac st
  | Assn assn c =>
    sample (mapim_p (fun _ e => dirac (eval_zexpr st e)) assn)
      (fun assn' => run c (upd st assn'))
  | If e cthen celse c =>
    let branch := if eval_bexpr st e then cthen else celse in
    sample (run branch st) (run c)
  | Block vs block c =>
    let old := state_of_fun vs st in
    let new := upd st (mkfmapf (fun _ => 0%R) vs) in
    sample (run block new)
      (fun st' => run c (upd st' (mkfmapf old vs)))
  end.
