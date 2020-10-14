Require Import Coq.Strings.String.
Require Import Coq.Unicode.Utf8.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice 
  seq ssrint rat ssralg ssrnum.

From extructures Require Import ord fset.

From deriving Require Import deriving.

From RandC Require Import Extra.

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
Definition var_countMixin := [derive countMixin for var].
Canonical var_countType := Eval hnf in CountType var var_countMixin.

Inductive symbol :=
| SVar of var
| SFor of nat.

Coercion SVar : var >-> symbol.

Definition var_of_sym (s : symbol) : option var :=
  if s is SVar v then Some v else None.

Lemma SVarK : pcancel SVar var_of_sym.
Proof. by case. Qed.

Definition symbol_indMixin := [indMixin for symbol_rect].
Canonical symbol_indType := Eval hnf in IndType _ symbol symbol_indMixin.
Definition symbol_eqMixin := [derive eqMixin for symbol].
Canonical symbol_eqType := Eval hnf in EqType symbol symbol_eqMixin.
Definition symbol_choiceMixin := [derive choiceMixin for symbol].
Canonical symbol_choiceType := Eval hnf in ChoiceType symbol symbol_choiceMixin.
Definition symbol_ordMixin := [derive ordMixin for symbol].
Canonical symbol_ordType := Eval hnf in OrdType symbol symbol_ordMixin.
Definition symbol_countMixin := [derive countMixin for symbol].
Canonical symbol_countType := Eval hnf in CountType symbol symbol_countMixin.

Inductive comp_op :=
| Leq
| Ltq.

Definition comp_op_indMixin := [indMixin for comp_op_rect].
Canonical comp_op_indType := Eval hnf in IndType _ comp_op comp_op_indMixin.
Definition comp_op_eqMixin := [derive eqMixin for comp_op].
Canonical comp_op_eqType := Eval hnf in EqType comp_op comp_op_eqMixin.
Definition comp_op_choiceMixin := [derive choiceMixin for comp_op].
Canonical comp_op_choiceType := Eval hnf in ChoiceType comp_op comp_op_choiceMixin.
Definition comp_op_ordMixin := [derive ordMixin for comp_op].
Canonical comp_op_ordType := Eval hnf in OrdType comp_op comp_op_ordMixin.
Definition comp_op_countMixin := [derive countMixin for comp_op].
Canonical comp_op_countType := Eval hnf in CountType comp_op comp_op_countMixin.

Inductive log_op :=
| And
| Or.

Definition log_op_indMixin := [indMixin for log_op_rect].
Canonical log_op_indType := Eval hnf in IndType _ log_op log_op_indMixin.
Definition log_op_eqMixin := [derive eqMixin for log_op].
Canonical log_op_eqType := Eval hnf in EqType log_op log_op_eqMixin.
Definition log_op_choiceMixin := [derive choiceMixin for log_op].
Canonical log_op_choiceType := Eval hnf in ChoiceType log_op log_op_choiceMixin.
Definition log_op_ordMixin := [derive ordMixin for log_op].
Canonical log_op_ordType := Eval hnf in OrdType log_op log_op_ordMixin.
Definition log_op_countMixin := [derive countMixin for log_op].
Canonical log_op_countType := Eval hnf in CountType log_op log_op_countMixin.

Inductive arith_op :=
| Plus
| Times
| Minus.

Definition arith_op_indMixin := [indMixin for arith_op_rect].
Canonical arith_op_indType := Eval hnf in IndType _ arith_op arith_op_indMixin.
Definition arith_op_eqMixin := [derive eqMixin for arith_op].
Canonical arith_op_eqType := Eval hnf in EqType arith_op arith_op_eqMixin.
Definition arith_op_choiceMixin := [derive choiceMixin for arith_op].
Canonical arith_op_choiceType := Eval hnf in ChoiceType arith_op arith_op_choiceMixin.
Definition arith_op_ordMixin := [derive ordMixin for arith_op].
Canonical arith_op_ordType := Eval hnf in OrdType arith_op arith_op_ordMixin.
Definition arith_op_countMixin := [derive countMixin for arith_op].
Canonical arith_op_countType := Eval hnf in CountType arith_op arith_op_countMixin.

Inductive trunc_op :=
| Ceil
| Floor.

Definition trunc_op_indMixin := [indMixin for trunc_op_rect].
Canonical trunc_op_indType := Eval hnf in IndType _ trunc_op trunc_op_indMixin.
Definition trunc_op_eqMixin := [derive eqMixin for trunc_op].
Canonical trunc_op_eqType := Eval hnf in EqType trunc_op trunc_op_eqMixin.
Definition trunc_op_choiceMixin := [derive choiceMixin for trunc_op].
Canonical trunc_op_choiceType := Eval hnf in ChoiceType trunc_op trunc_op_choiceMixin.
Definition trunc_op_ordMixin := [derive ordMixin for trunc_op].
Canonical trunc_op_ordType := Eval hnf in OrdType trunc_op trunc_op_ordMixin.
Definition trunc_op_countMixin := [derive countMixin for trunc_op].
Canonical trunc_op_countType := Eval hnf in CountType trunc_op trunc_op_countMixin.

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
| ZSym   of symbol
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
  | ZSym v => f v
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
  | BTest be be1 be2 =>
    BTest (subst_bexpr f be) (subst_bexpr f be1) (subst_bexpr f be2)
  | BCompZ o ze1 ze2 => BCompZ o (subst_zexpr f ze1) (subst_zexpr f ze2)
  | BCompQ o qe1 qe2 => BCompQ o (subst_qexpr f qe1) (subst_qexpr f qe2)
  | BLogOp o be1 be2 => BLogOp o (subst_bexpr f be1) (subst_bexpr f be2)
  | BNot be => BNot (subst_bexpr f be)
  end

with subst_zexpr f ze : zexpr :=
  match ze with
  | ZSym v => f v
  | ZConst _ => ze
  | ZTest be ze1 ze2 =>
    ZTest (subst_bexpr f be) (subst_zexpr f ze1) (subst_zexpr f ze2)
  | ZArith o ze1 ze2 =>
    ZArith o (subst_zexpr f ze1) (subst_zexpr f ze2)
  | ZTrunc o qe =>
    ZTrunc o (subst_qexpr f qe)
  end

with subst_qexpr f qe : qexpr :=
  match qe with
  | QConst _ => qe
  | QTest be qe1 qe2 =>
    QTest (subst_bexpr f be) (subst_qexpr f qe1) (subst_qexpr f qe2)
  | QArith o qe1 qe2 => QArith o (subst_qexpr f qe1) (subst_qexpr f qe2)
  | QOfZ ze => QOfZ (subst_zexpr f ze)
  end.

Ltac solve_subst_exprP :=
  match goal with
  | [e : ?x = ?y |- context[?x]] =>
    rewrite {}e
  end.

Lemma subst_exprP f g :
  (forall e,
      eval_bexpr f (subst_bexpr g e) =
      eval_bexpr (fun v => eval_zexpr f (g v)) e) /\
  (forall e,
      eval_zexpr f (subst_zexpr g e) =
      eval_zexpr (fun v => eval_zexpr f (g v)) e) /\
  (forall e,
      eval_qexpr f (subst_qexpr g e) =
      eval_qexpr (fun v => eval_zexpr f (g v)) e).
Proof.
apply: expr_ind=> //=; try by (move=> *; repeat solve_subst_exprP).
Qed.

Lemma subst_bexprP f g e :
  eval_bexpr f (subst_bexpr g e) =
  eval_bexpr (fun v => eval_zexpr f (g v)) e.
Proof.
by case: (subst_exprP f g)=> [?[??]].
Qed.

Lemma subst_zexprP f g e :
  eval_zexpr f (subst_zexpr g e) =
  eval_zexpr (fun v => eval_zexpr f (g v)) e.
Proof.
by case: (subst_exprP f g)=> [?[??]].
Qed.

Lemma subst_qexprP f g e :
  eval_qexpr f (subst_qexpr g e) =
  eval_qexpr (fun v => eval_zexpr f (g v)) e.
Proof.
by case: (subst_exprP f g)=> [?[??]].
Qed.

End Eval.

Section Instances.

Import GenTree.

Fixpoint tree_of_bexpr be : tree nat :=
  match be with
  | BConst b =>
    Node 0 [:: Leaf (pickle b)]
  | BEqB be1 be2 =>
    Node 1 [:: tree_of_bexpr be1; tree_of_bexpr be2]
  | BEqZ ze1 ze2 =>
    Node 2 [:: tree_of_zexpr ze1; tree_of_zexpr ze2]
  | BEqQ qe1 qe2 =>
    Node 3 [:: tree_of_qexpr qe1; tree_of_qexpr qe2]
  | BTest be1 be2 be3 =>
    Node 4 [:: tree_of_bexpr be1; tree_of_bexpr be2; tree_of_bexpr be3]
  | BCompZ co ze1 ze2 =>
    Node 5 [:: Leaf (pickle co); tree_of_zexpr ze1; tree_of_zexpr ze2]
  | BCompQ co qe1 qe2 =>
    Node 6 [:: Leaf (pickle co); tree_of_qexpr qe1; tree_of_qexpr qe2]
  | BLogOp lo be1 be2 =>
    Node 7 [:: Leaf (pickle lo); tree_of_bexpr be1; tree_of_bexpr be2]
  | BNot be =>
    Node 8 [:: tree_of_bexpr be]
  end

with tree_of_zexpr ze : tree nat :=
  match ze with
  | ZSym s =>
    Node 0 [:: Leaf (pickle s)]
  | ZConst n =>
    Node 1 [:: Leaf (pickle n)]
  | ZTest be ze1 ze2 =>
    Node 2 [:: tree_of_bexpr be; tree_of_zexpr ze1; tree_of_zexpr ze2]
  | ZArith ao ze1 ze2 =>
    Node 3 [:: Leaf (pickle ao); tree_of_zexpr ze1; tree_of_zexpr ze2]
  | ZTrunc to qe =>
    Node 4 [:: Leaf (pickle to); tree_of_qexpr qe]
  end

with tree_of_qexpr qe : tree nat :=
  match qe with
  | QConst q =>
    Node 0 [:: Leaf (pickle q)]
  | QTest be qe1 qe2 =>
    Node 1 [:: tree_of_bexpr be; tree_of_qexpr qe1; tree_of_qexpr qe2]
  | QArith ao qe1 qe2 =>
    Node 2 [:: Leaf (pickle ao); tree_of_qexpr qe1; tree_of_qexpr qe2]
  | QOfZ ze =>
    Node 3 [:: tree_of_zexpr ze]
  end.

Definition unpickle_def {T : countType} (def : T) (n : nat) : T :=
  odflt def (unpickle n).

Lemma pickleK' (T : countType) (def : T) : cancel pickle (unpickle_def def).
Proof. by move=> x; rewrite /unpickle_def pickleK. Qed.

Fixpoint bexpr_of_tree (be : tree nat) : bexpr :=
  match be with
  | Node 0 [:: Leaf b] =>
    BConst (unpickle_def true b)
  | Node 1 [:: be1; be2] =>
    BEqB (bexpr_of_tree be1) (bexpr_of_tree be2)
  | Node 2 [:: ze1; ze2] =>
    BEqZ (zexpr_of_tree ze1) (zexpr_of_tree ze2)
  | Node 3 [:: qe1; qe2] =>
    BEqQ (qexpr_of_tree qe1) (qexpr_of_tree qe2)
  | Node 4 [:: be1; be2; be3] =>
    BTest (bexpr_of_tree be1) (bexpr_of_tree be2) (bexpr_of_tree be3)
  | Node 5 [:: Leaf co; ze1; ze2] =>
    BCompZ (unpickle_def Leq co) (zexpr_of_tree ze1) (zexpr_of_tree ze2)
  | Node 6 [:: Leaf co; qe1; qe2] =>
    BCompQ (unpickle_def Leq co) (qexpr_of_tree qe1) (qexpr_of_tree qe2)
  | Node 7 [:: Leaf lo; be1; be2] =>
    BLogOp (unpickle_def And lo) (bexpr_of_tree be1) (bexpr_of_tree be2)
  | Node 8 [:: be] => BNot (bexpr_of_tree be)
  | _ => BConst false
  end

with zexpr_of_tree ze : zexpr :=
  match ze with
  | Node 0 [:: Leaf s] =>
    ZSym (unpickle_def (SFor 0) s)
  | Node 1 [:: Leaf n] =>
    ZConst (unpickle_def (0 : int) n)
  | Node 2 [:: be; ze1; ze2] =>
    ZTest (bexpr_of_tree be) (zexpr_of_tree ze1) (zexpr_of_tree ze2)
  | Node 3 [:: Leaf ao; ze1; ze2] =>
    ZArith (unpickle_def Plus ao) (zexpr_of_tree ze1) (zexpr_of_tree ze2)
  | Node 4 [:: Leaf to; qe] =>
    ZTrunc (unpickle_def Ceil to) (qexpr_of_tree qe)
  | _ => ZConst 0
  end

with qexpr_of_tree qe : qexpr :=
  match qe with
  | Node 0 [:: Leaf q] =>
    QConst (unpickle_def 0%Q q)
  | Node 1 [:: be; qe1; qe2] =>
    QTest (bexpr_of_tree be) (qexpr_of_tree qe1) (qexpr_of_tree qe2)
  | Node 2 [:: Leaf ao; qe1; qe2] =>
    QArith (unpickle_def Plus ao) (qexpr_of_tree qe1) (qexpr_of_tree qe2)
  | Node 3 [:: ze] =>
    QOfZ (zexpr_of_tree ze)
  | _ => QConst 0
  end.

Lemma tree_of_exprK : cancel tree_of_bexpr bexpr_of_tree /\
                      cancel tree_of_zexpr zexpr_of_tree /\
                      cancel tree_of_qexpr qexpr_of_tree.
Proof.
apply: expr_ind=> // *;
by rewrite /= ?pickleK' //;
repeat match goal with
| H : ?x = _ |- context[?x] => rewrite {}H //
end.
Qed.

Lemma tree_of_bexprK : cancel tree_of_bexpr bexpr_of_tree.
Proof. by case: tree_of_exprK=> [? [??]]. Qed.

Lemma tree_of_zexprK : cancel tree_of_zexpr zexpr_of_tree.
Proof. by case: tree_of_exprK=> [? [??]]. Qed.

Lemma tree_of_qexprK : cancel tree_of_qexpr qexpr_of_tree.
Proof. by case: tree_of_exprK=> [? [??]]. Qed.

Lemma bexpr_eqMixin : Equality.mixin_of bexpr.
Proof. exact: CanEqMixin tree_of_bexprK. Qed.
Canonical bexpr_eqType := EqType bexpr bexpr_eqMixin.
Lemma bexpr_choiceMixin : Choice.mixin_of bexpr.
Proof. exact: CanChoiceMixin tree_of_bexprK. Qed.
Canonical bexpr_choiceType := Eval hnf in ChoiceType bexpr bexpr_choiceMixin.
Lemma bexpr_ordMixin : Ord.mixin_of bexpr.
Proof. exact: CanOrdMixin tree_of_bexprK. Qed.
Canonical bexpr_ordType := Eval hnf in OrdType bexpr bexpr_ordMixin.

Lemma zexpr_eqMixin : Equality.mixin_of zexpr.
Proof. exact: CanEqMixin tree_of_zexprK. Qed.
Canonical zexpr_eqType := EqType zexpr zexpr_eqMixin.
Lemma zexpr_choiceMixin : Choice.mixin_of zexpr.
Proof. exact: CanChoiceMixin tree_of_zexprK. Qed.
Canonical zexpr_choiceType := Eval hnf in ChoiceType zexpr zexpr_choiceMixin.
Lemma zexpr_ordMixin : Ord.mixin_of zexpr.
Proof. exact: CanOrdMixin tree_of_zexprK. Qed.
Canonical zexpr_ordType := Eval hnf in OrdType zexpr zexpr_ordMixin.

Lemma qexpr_eqMixin : Equality.mixin_of qexpr.
Proof. exact: CanEqMixin tree_of_qexprK. Qed.
Canonical qexpr_eqType := EqType qexpr qexpr_eqMixin.
Lemma qexpr_choiceMixin : Choice.mixin_of qexpr.
Proof. exact: CanChoiceMixin tree_of_qexprK. Qed.
Canonical qexpr_choiceType := Eval hnf in ChoiceType qexpr qexpr_choiceMixin.
Lemma qexpr_ordMixin : Ord.mixin_of qexpr.
Proof. exact: CanOrdMixin tree_of_qexprK. Qed.
Canonical qexpr_ordType := Eval hnf in OrdType qexpr qexpr_ordMixin.

End Instances.

Fixpoint bexpr_syms be :=
  match be with
  | BConst _         => fset0
  | BEqB be1 be2     => bexpr_syms be1 :|: bexpr_syms be2
  | BEqZ ze1 ze2     => zexpr_syms ze1 :|: zexpr_syms ze2
  | BEqQ qe1 qe2     => qexpr_syms qe1 :|: qexpr_syms qe2
  | BTest be be1 be2 => bexpr_syms be  :|: bexpr_syms be1 :|: bexpr_syms be2
  | BCompZ _ ze1 ze2 => zexpr_syms ze1 :|: zexpr_syms ze2
  | BCompQ _ qe1 qe2 => qexpr_syms qe1 :|: qexpr_syms qe2
  | BLogOp _ be1 be2 => bexpr_syms be1 :|: bexpr_syms be2
  | BNot be          => bexpr_syms be
  end

with zexpr_syms ze :=
  match ze with
  | ZSym v           => fset1 v
  | ZConst _         => fset0
  | ZTest be ze1 ze2 => bexpr_syms be  :|: zexpr_syms ze1 :|: zexpr_syms ze2
  | ZArith _ ze1 ze2 => zexpr_syms ze1 :|: zexpr_syms ze2
  | ZTrunc _ qe      => qexpr_syms qe
  end

with qexpr_syms qe :=
  match qe with
  | QConst _         => fset0
  | QTest be qe1 qe2 => bexpr_syms be  :|: qexpr_syms qe1 :|: qexpr_syms qe2
  | QArith _ qe1 qe2 => qexpr_syms qe1 :|: qexpr_syms qe2
  | QOfZ ze          => zexpr_syms ze
  end.

Ltac solve_eq_in_eval_exprP :=
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

Implicit Types V : {fset symbol}.

Lemma eq_in_eval_expr V f g :
  {in V, f =1 g} ->
  (forall be, fsubset (bexpr_syms be) V ->
              eval_bexpr f be = eval_bexpr g be) /\
  (forall ze, fsubset (zexpr_syms ze) V ->
              eval_zexpr f ze = eval_zexpr g ze) /\
  (forall qe, fsubset (qexpr_syms qe) V ->
              eval_qexpr f qe = eval_qexpr g qe).
Proof.
move=> efg; apply: expr_ind=> //=; try by solve_eq_in_eval_exprP.
move=> v; rewrite fsub1set; exact: efg.
Qed.

Lemma eq_in_eval_bexpr V f g :
  {in V, f =1 g} ->
  forall e, fsubset (bexpr_syms e) V ->
  eval_bexpr f e = eval_bexpr g e.
Proof. by move=> /eq_in_eval_expr [? [? ?]]. Qed.

Lemma eq_in_eval_zexpr V f g :
  {in V, f =1 g} ->
  forall e, fsubset (zexpr_syms e) V ->
  eval_zexpr f e = eval_zexpr g e.
Proof. by move=> /eq_in_eval_expr [? [? ?]]. Qed.

Lemma eq_eval_bexpr f g :
  f =1 g ->
  forall e, eval_bexpr f e = eval_bexpr g e.
Proof.
move=> fg ?; apply: eq_in_eval_bexpr (fsubsetxx _).
move=> ??; exact: fg.
Qed.

Lemma eq_eval_zexpr f g :
  f =1 g ->
  forall e, eval_zexpr f e = eval_zexpr g e.
Proof.
move=> fg ?; apply: eq_in_eval_zexpr (fsubsetxx _).
move=> ??; exact: fg.
Qed.

Definition formulas := seq (nat * zexpr).

Fixpoint feval_forms (defs : formulas) st (f : nat) : int :=
  if defs is (f', e) :: fs then
    if f' == f then
      let eval s := match s with
                    | SVar v => st v
                    | SFor f => feval_forms fs st f
                    end in
      eval_zexpr eval e
    else feval_forms fs st f
  else 0.

Definition feval_sym defs st s : int :=
  match s with
  | SVar v => st v
  | SFor f => feval_forms defs st f
  end.

Fixpoint formula_vars (defs : formulas) (f : nat) : {fset var} :=
  if defs is (f', e) :: defs then
    if f' == f then
      \bigcup_(s <- zexpr_syms e)
         match s with
         | SVar v   => fset1 v
         | SFor f'' => formula_vars defs f''
         end
    else formula_vars defs f
  else fset0.

Definition sym_vars defs s : {fset var} :=
  match s with
  | SVar v => fset1 v
  | SFor f => formula_vars defs f
  end.

Lemma eq_in_feval_sym defs st1 st2 s :
  {in sym_vars defs s, st1 =1 st2} ->
  feval_sym defs st1 s = feval_sym defs st2 s.
Proof.
case: s=> [v|f] /= est; first by apply: est; exact/fset1P.
elim: defs f est=> [|[f e] defs IH] //= f'.
case: (altP (f =P f'))=> [{f'} _|ne] est; last exact: IH.
apply/eq_in_eval_zexpr; last exact/fsubsetxx.
move=> [v|f'] in_e.
  by apply: est; apply/bigcupP; exists (SVar v); rewrite // in_fset1 eqxx.
by apply: IH=> // v in_f'; apply: est; apply/bigcupP; exists (SFor f').
Qed.

Definition feval_bexpr defs st e :=
  eval_bexpr (feval_sym defs st) e.

Definition feval_zexpr defs st e :=
  eval_zexpr (feval_sym defs st) e.

Definition feval_qexpr defs st e :=
  eval_qexpr (feval_sym defs st) e.

Definition bexpr_vars defs e :=
  \bigcup_(s <- bexpr_syms e) sym_vars defs s.

Definition zexpr_vars defs e :=
  \bigcup_(s <- zexpr_syms e) sym_vars defs s.

Definition qexpr_vars defs e :=
  \bigcup_(s <- qexpr_syms e) sym_vars defs s.

Lemma eq_in_feval_bexpr defs st1 st2 e :
  {in bexpr_vars defs e, st1 =1 st2} ->
  feval_bexpr defs st1 e = feval_bexpr defs st2 e.
Proof.
move=> est; rewrite /feval_bexpr /bexpr_vars.
apply/eq_in_eval_bexpr; last exact: fsubsetxx.
move=> s s_e; apply: eq_in_feval_sym=> v v_s.
by apply: est; apply/bigcupP; exists s.
Qed.

Lemma eq_in_feval_zexpr defs st1 st2 e :
  {in zexpr_vars defs e, st1 =1 st2} ->
  feval_zexpr defs st1 e = feval_zexpr defs st2 e.
Proof.
move=> est; rewrite /feval_zexpr /zexpr_vars.
apply/eq_in_eval_zexpr; last exact: fsubsetxx.
move=> s s_e; apply: eq_in_feval_sym=> v v_s.
by apply: est; apply/bigcupP; exists s.
Qed.
