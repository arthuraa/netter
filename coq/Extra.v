From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype path
  ssrint rat bigop.

From extructures Require Import ord fset fmap ffun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.

Definition int_ordMixin := CanOrdMixin natsum_of_intK.
Canonical int_ordType := Eval hnf in OrdType int int_ordMixin.

Definition rat_ordMixin := [ordMixin of rat by <:].
Canonical rat_ordType := Eval hnf in OrdType rat rat_ordMixin.

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

Arguments bigcupP {_ _ _ _ _ _}.
Arguments mkfmap {_ _}.
