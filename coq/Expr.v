Require Import Coq.Strings.String.
Require Import Coq.Unicode.Utf8.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice ssrint
  rat ssralg ssrnum.

From extructures Require Import ord fset.

From void Require Import void.

From deriving Require Import deriving.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.

Inductive var := Var {vname : string; vnum : nat}.

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

Unset Elimination Schemes.
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
Set Elimination Schemes.

Scheme bexpr_rect := Induction for bexpr Sort Type
with   zexpr_rect := Induction for zexpr Sort Type
with   qexpr_rect := Induction for qexpr Sort Type.

Combined Scheme expr_rect from bexpr_rect, zexpr_rect, qexpr_rect.

Scheme bexpr_ind := Induction for bexpr Sort Prop
with   zexpr_ind := Induction for zexpr Sort Prop
with   qexpr_ind := Induction for qexpr Sort Prop.

Combined Scheme expr_ind from bexpr_ind, zexpr_ind, qexpr_ind.

Section Eval.

Implicit Types (be : bexpr) (ze : zexpr) (qe : qexpr).

Fixpoint eval_bexpr f be : bool :=
  match be with
  | BConst b => b
  | BEqB be1 be2 => eval_bexpr f be1 == eval_bexpr f be2
  | BEqZ ze1 ze2 => eval_zexpr f ze1 == eval_zexpr f ze2
  | BEqQ qe1 qe2 => eval_qexpr f qe1 == eval_qexpr f qe2
  | BTest be be1 be2 => if eval_bexpr f be then eval_bexpr f be1
                        else eval_bexpr f be2
  | BCompZ Leq ze1 ze2 => (eval_zexpr f ze1 <= eval_zexpr f ze2)%R
  | BCompZ Ltq ze1 ze2 => (eval_zexpr f ze1 <  eval_zexpr f ze2)%R
  | BCompQ Leq qe1 qe2 => (eval_qexpr f qe1 <= eval_qexpr f qe2)%R
  | BCompQ Ltq qe1 qe2 => (eval_qexpr f qe1 <  eval_qexpr f qe2)%R
  | BLogOp And be1 be2 => eval_bexpr f be1 && eval_bexpr f be2
  | BLogOp Or  be1 be2 => eval_bexpr f be1 || eval_bexpr f be2
  | BNot be => ~~ eval_bexpr f be
  end

with eval_zexpr f ze : int :=
  match ze with
  | ZVar v => f v
  | ZConst n => n
  | ZTest be ze1 ze2 => if eval_bexpr f be then eval_zexpr f ze1
                        else eval_zexpr f ze2
  | ZArith Plus ze1 ze2 => eval_zexpr f ze1 + eval_zexpr f ze2
  | ZArith Times ze1 ze2 => eval_zexpr f ze1 * eval_zexpr f ze2
  | ZArith Minus ze1 ze2 => eval_zexpr f ze1 - eval_zexpr f ze2
  | ZTrunc _ _ => 0 (* FIXME *)
  end

with eval_qexpr f qe : rat :=
  match qe with
  | QConst x => x
  | QTest be qe1 qe2 => if eval_bexpr f be then eval_qexpr f qe1
                        else eval_qexpr f qe2
  | QArith Plus qe1 qe2 => eval_qexpr f qe1 + eval_qexpr f qe2
  | QArith Times qe1 qe2 => eval_qexpr f qe1 * eval_qexpr f qe2
  | QArith Minus qe1 qe2 => eval_qexpr f qe1 - eval_qexpr f qe2
  | QOfZ ze => ratz (eval_zexpr f ze)
  end.

Fixpoint subst_bexpr f be : bexpr :=
  match be with
  | BConst _ => be
  | BEqB be1 be2 => BEqB (subst_bexpr f be1) (subst_bexpr f be2)
  | BEqZ ze1 ze2 => BEqZ (subst_zexpr f ze1) (subst_zexpr f ze2)
  | BEqQ qe1 qe2 => BEqQ (subst_qexpr f qe1) (subst_qexpr f qe2)
  | BTest be be1 be2 => BTest (subst_bexpr f be) (subst_bexpr f be1) (subst_bexpr f be2)
  | BCompZ o ze1 ze2 => BCompZ o (subst_zexpr f ze1) (subst_zexpr f ze2)
  | BCompQ o qe1 qe2 => BCompQ o (subst_qexpr f qe1) (subst_qexpr f qe2)
  | BLogOp o be1 be2 => BLogOp o (subst_bexpr f be1) (subst_bexpr f be2)
  | BNot be => BNot (subst_bexpr f be)
  end

with subst_zexpr f ze : zexpr :=
  match ze with
  | ZVar v => f v
  | ZConst _ => ze
  | ZTest be ze1 ze2 => ZTest (subst_bexpr f be) (subst_zexpr f ze1) (subst_zexpr f ze2)
  | ZArith o ze1 ze2 => ZArith o (subst_zexpr f ze1) (subst_zexpr f ze2)
  | ZTrunc o qe => ZTrunc o (subst_qexpr f qe)
  end

with subst_qexpr f qe : qexpr :=
  match qe with
  | QConst _ => qe
  | QTest be qe1 qe2 => QTest (subst_bexpr f be) (subst_qexpr f qe1) (subst_qexpr f qe2)
  | QArith o qe1 qe2 => QArith o (subst_qexpr f qe1) (subst_qexpr f qe2)
  | QOfZ ze => QOfZ (subst_zexpr f ze)
  end.

End Eval.

Axiom zexpr_eqMixin : Equality.mixin_of zexpr.
Canonical zexpr_eqType := EqType zexpr zexpr_eqMixin.
Axiom zexpr_choiceMixin : Choice.mixin_of zexpr.
Canonical zexpr_choiceType := Eval hnf in ChoiceType zexpr zexpr_choiceMixin.
Axiom zexpr_ordMixin : Ord.mixin_of zexpr.
Canonical zexpr_ordType := Eval hnf in OrdType zexpr zexpr_ordMixin.

Fixpoint bexpr_vars be :=
  match be with
  | BConst _         => fset0
  | BEqB be1 be2     => bexpr_vars be1 :|: bexpr_vars be2
  | BEqZ ze1 ze2     => zexpr_vars ze1 :|: zexpr_vars ze2
  | BEqQ qe1 qe2     => qexpr_vars qe1 :|: qexpr_vars qe2
  | BTest be be1 be2 => bexpr_vars be  :|: bexpr_vars be1 :|: bexpr_vars be2
  | BCompZ _ ze1 ze2 => zexpr_vars ze1 :|: zexpr_vars ze2
  | BCompQ _ qe1 qe2 => qexpr_vars qe1 :|: qexpr_vars qe2
  | BLogOp _ be1 be2 => bexpr_vars be1 :|: bexpr_vars be2
  | BNot be          => bexpr_vars be
  end

with zexpr_vars ze :=
  match ze with
  | ZVar v           => fset1 v
  | ZConst _         => fset0
  | ZTest be ze1 ze2 => bexpr_vars be  :|: zexpr_vars ze1 :|: zexpr_vars ze2
  | ZArith _ ze1 ze2 => zexpr_vars ze1 :|: zexpr_vars ze2
  | ZTrunc _ qe      => qexpr_vars qe
  end

with qexpr_vars qe :=
  match qe with
  | QConst _         => fset0
  | QTest be qe1 qe2 => bexpr_vars be  :|: qexpr_vars qe1 :|: qexpr_vars qe2
  | QArith _ qe1 qe2 => qexpr_vars qe1 :|: qexpr_vars qe2
  | QOfZ ze          => zexpr_vars ze
  end.

Ltac solve_expr_varsP :=
  move=> *;
  repeat match goal with
         | [H : is_true (fsubset (_ :|: _) _) |- _] =>
           rewrite fsubUset in H
         | [H : is_true (_ && _) |- _] =>
           case/andP: H=> ??
         | [IH : ?P -> _, H : ?P |- _] =>
           move/(_ H) in IH
         | [H : ?x = _ |- context[?x]] => rewrite {}H
         | [x : _ |- _] =>
           match goal with
           | [ |- context[match x with _ => _ end]] =>
             case: x=> * /=
           end
         end.

Implicit Types V : {fset var}.

Lemma expr_varsP V f g :
  {in V, f =1 g} ->
  (forall be, fsubset (bexpr_vars be) V ->
              eval_bexpr f be = eval_bexpr g be) /\
  (forall ze, fsubset (zexpr_vars ze) V ->
              eval_zexpr f ze = eval_zexpr g ze) /\
  (forall qe, fsubset (qexpr_vars qe) V ->
              eval_qexpr f qe = eval_qexpr g qe).
Proof.
move=> efg; apply: expr_ind=> //=; try by solve_expr_varsP.
move=> v; rewrite fsub1set; exact: efg.
Qed.

Lemma bexpr_varsP V f g :
  {in V, f =1 g} ->
  forall ze, fsubset (bexpr_vars ze) V ->
  eval_bexpr f ze = eval_bexpr g ze.
Proof. by move=> /expr_varsP [? [? ?]]. Qed.

Lemma zexpr_varsP V f g :
  {in V, f =1 g} ->
  forall ze, fsubset (zexpr_vars ze) V ->
  eval_zexpr f ze = eval_zexpr g ze.
Proof. by move=> /expr_varsP [? [? ?]]. Qed.
