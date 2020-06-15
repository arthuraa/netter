Require Import Coq.Strings.String.
Require Import Coq.Unicode.Utf8.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice ssrint
  rat ssralg ssrnum.

From extructures Require Import ord.

From void Require Import void.

From deriving Require Import deriving.

Inductive var := Var of string & nat.

Definition var_indMixin := Eval simpl in [indMixin for var_rect].
Canonical var_indType := IndType _ var var_indMixin.
Definition var_eqMixin := Eval simpl in [derive eqMixin for var].
Canonical var_eqType := EqType var var_eqMixin.
Definition var_choiceMixin := [derive choiceMixin for var].
Canonical var_choiceType := Eval hnf in ChoiceType var var_choiceMixin.
Definition var_ordMixin := Eval simpl in [derive ordMixin for var].
Canonical var_ordType := OrdType var var_ordMixin.

Inductive comp_op :=
| Leq
| Ltq.

Inductive log_op :=
| And
| Or.

Inductive arith_op :=
| Plus
| Times
| Minus.

Inductive trunc_op :=
| Ceil
| Floor.

Inductive bexpr :=
| BConst of bool
| BEqB   of bexpr & bexpr
| BEqZ   of zexpr & zexpr
| BEqQ   of qexpr & qexpr
| BTest  of bexpr & bexpr & bexpr
| BCompZ of comp_op & zexpr & zexpr
| BCompQ of comp_op & qexpr & qexpr
| BLogOp of log_op & bexpr & bexpr
| BNot   of bexpr

with zexpr :=
| ZVar   of var
| ZConst of int
| ZTest  of bexpr & zexpr & zexpr
| ZArith of arith_op & zexpr & zexpr
| ZTrunc of trunc_op & qexpr

with qexpr :=
| QConst of rat
| QTest  of bexpr & qexpr & qexpr
| QArith of arith_op & qexpr & qexpr
| QOfZ   of zexpr.

Section Eval.

Implicit Types (be : bexpr) (ze : zexpr) (qe : qexpr).

Variable f : var → int.

Fixpoint eval_bexpr be : bool :=
  match be with
  | BConst b => b
  | BEqB be1 be2 => eval_bexpr be1 == eval_bexpr be2
  | BEqZ ze1 ze2 => eval_zexpr ze1 == eval_zexpr ze2
  | BEqQ qe1 qe2 => eval_qexpr qe1 == eval_qexpr qe2
  | BTest be be1 be2 => if eval_bexpr be then eval_bexpr be1
                        else eval_bexpr be2
  | BCompZ Leq ze1 ze2 => (eval_zexpr ze1 <= eval_zexpr ze2)%R
  | BCompZ Ltq ze1 ze2 => (eval_zexpr ze1 <  eval_zexpr ze2)%R
  | BCompQ Leq qe1 qe2 => (eval_qexpr qe1 <= eval_qexpr qe2)%R
  | BCompQ Ltq qe1 qe2 => (eval_qexpr qe1 <  eval_qexpr qe2)%R
  | BLogOp And be1 be2 => eval_bexpr be1 && eval_bexpr be2
  | BLogOp Or  be1 be2 => eval_bexpr be1 || eval_bexpr be2
  | BNot be => ~~ eval_bexpr be
  end

with eval_zexpr ze : int :=
  match ze with
  | ZVar v => f v
  | ZConst n => n
  | ZTest be ze1 ze2 => if eval_bexpr be then eval_zexpr ze1
                        else eval_zexpr ze2
  | ZArith Plus ze1 ze2 => eval_zexpr ze1 + eval_zexpr ze2
  | ZArith Times ze1 ze2 => eval_zexpr ze1 * eval_zexpr ze2
  | ZArith Minus ze1 ze2 => eval_zexpr ze1 - eval_zexpr ze2
  | ZTrunc _ _ => 0 (* FIXME *)
  end

with eval_qexpr qe : rat :=
  match qe with
  | QConst x => x
  | QTest be qe1 qe2 => if eval_bexpr be then eval_qexpr qe1
                        else eval_qexpr qe2
  | QArith Plus qe1 qe2 => eval_qexpr qe1 + eval_qexpr qe2
  | QArith Times qe1 qe2 => eval_qexpr qe1 * eval_qexpr qe2
  | QArith Minus qe1 qe2 => eval_qexpr qe1 - eval_qexpr qe2
  | QOfZ ze => ratz (eval_zexpr ze)
  end.

End Eval.

Axiom zexpr_eqMixin : Equality.mixin_of zexpr.
Canonical zexpr_eqType := EqType zexpr zexpr_eqMixin.
Axiom zexpr_choiceMixin : Choice.mixin_of zexpr.
Canonical zexpr_choiceType := Eval hnf in ChoiceType zexpr zexpr_choiceMixin.
Axiom zexpr_ordMixin : Ord.mixin_of zexpr.
Canonical zexpr_ordType := Eval hnf in OrdType zexpr zexpr_ordMixin.
