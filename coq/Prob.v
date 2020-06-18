Require Import Coq.Strings.String.
Require Import Coq.Unicode.Utf8.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq
  ssrint rat ssralg ssrnum bigop.

From extructures Require Import ord fset fmap.

From void Require Import void.

From deriving Require Import deriving.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* MOVE *)
Lemma val_fset_filter (T : ordType) (P : T -> bool) (X : {fset T}) :
  fset_filter P X = filter P X :> seq T.
Proof.
apply: (path.eq_sorted (@Ord.lt_trans T)).
- move=> x y /andP [/Ord.ltW xy /Ord.ltW yx].
  by apply: Ord.anti_leq; rewrite xy.
- rewrite /fset_filter /fset unlock /=.
  exact: FSet.fset_subproof.
- rewrite path.sorted_filter ?valP //.
  exact: Ord.lt_trans.
rewrite uniq_perm ?filter_uniq ?uniq_fset //.
by move=> x; rewrite /= in_fset_filter mem_filter.
Qed.

Arguments bigcupP {_ _ _ _ _ _}.
Arguments mkfmap {_ _}.
(* /MOVE *)


Axiom int_ordMixin : Ord.mixin_of int.
Canonical int_ordType := Eval hnf in OrdType int int_ordMixin.

Definition rat_ordMixin := [ordMixin of rat by <:].
Canonical rat_ordType := Eval hnf in OrdType rat rat_ordMixin.

Local Open Scope ring_scope.
Local Open Scope fset_scope.

Section Prob.

Variable T : ordType.
Implicit Types (x : T) (X : {fset T}) (f : T -> rat).

Record distr := Distr {dval : {fmap T -> {x : rat | 0 < x}}}.
Definition distr_of & phant T := distr.
Notation "{ 'distr'  T }" := (distr_of (Phant T))
  (at level 0, format "{ 'distr'  T }") : form_scope.
Identity Coercion distr_of_distr : distr_of >-> distr.

Canonical distr_newType  := [newType for dval].
Definition distr_eqMixin := [eqMixin of distr by <:].
Canonical distr_eqType   := EqType distr distr_eqMixin.
Definition distr_choiceMixin := [choiceMixin of distr by <:].
Canonical distr_choiceType := Eval hnf in ChoiceType distr distr_choiceMixin.
Definition distr_ordMixin := [ordMixin of distr by <:].
Canonical distr_ordType := Eval hnf in OrdType distr distr_ordMixin.

Canonical distr_of_newType := [subType of {distr T}].
Canonical distr_of_eqType  := [eqType of {distr T}].
Canonical distr_of_choiceType := [choiceType of {distr T}].
Canonical distr_of_ordType := [ordType of {distr T}].

Implicit Types (d : {distr T}).

Definition fun_of_distr (d : distr) (x : T) : rat :=
  if val d x is Some p then val p else 0%R.

Coercion fun_of_distr : distr >-> Funclass.

Lemma eq_distr d1 d2 : d1 =1 d2 <-> d1 = d2.
Proof.
split=> [e|-> //]; apply/val_inj.
apply/eq_fmap=> x; move: (e x).
rewrite /fun_of_distr.
case: (val d1 x) (val d2 x)=> [y1|] [y2|] //=.
- by move=> /val_inj ->.
- by move=> {}e; move: (valP y1); rewrite /=  e.
- by move=> {}e; move: (valP y2); rewrite /= -e.
Qed.

Lemma distr_ge0 d x : 0 <= d x.
Proof.
rewrite /fun_of_distr; case: (val d x)=> [m|//].
by apply/Num.Theory.ltrW/valP.
Qed.

Definition supp (d : {distr T}) : {fset T} :=
  domm (val d).

Lemma mem_supp d x : (x \in supp d) = (0 < d x).
Proof.
rewrite /fun_of_distr /supp mem_domm.
by case: (val d x)=> // r; rewrite valP.
Qed.

Lemma mem_suppN d x : (x \in supp d) = (d x != 0).
Proof.
by rewrite mem_supp Num.Theory.ltr_neqAle eq_sym distr_ge0 andbT.
Qed.

Lemma suppPn d x : reflect (d x = 0) (x \notin supp d).
Proof.
rewrite /fun_of_distr /supp mem_domm.
apply/(iffP idP); case: (val d x)=> // [[/= r rP] e].
by rewrite e in rP.
Qed.

Arguments suppPn {d x}.

Definition mass d := \sum_(x <- supp d) d x.

Lemma massE d X :
  fsubset (supp d) X -> mass d = \sum_(x <- X) d x.
Proof.
rewrite /mass => sub.
have -> : supp d = fset_filter (mem (supp d)) X.
  apply/eq_fset=> x; rewrite in_fset_filter /=.
  by case: (boolP (x \in supp d))=> // /(fsubsetP sub) ->.
rewrite val_fset_filter big_filter big_mkcond /=.
apply/eq_big=> // x _.
by rewrite /supp /fun_of_distr mem_domm; case: (val d x).
Qed.

Definition mkdistr (X : {fset T}) (f : T -> rat) :=
  Distr (mkfmapfp (insub \o f) X).

Lemma mkdistrE X f x :
  mkdistr X f x = if (x \in X) && (0 <= f x) then f x else 0%R.
Proof.
rewrite /mkdistr /fun_of_distr /= mkfmapfpE.
case: ifP=> //= _; case: insubP=> [m pos e //|].
  by rewrite (Num.Theory.ltrW pos).
by case: (Num.Theory.sgrP (f x)).
Qed.

Lemma supp_mkdistr X f : supp (mkdistr X f) = fset_filter (fun x => 0 < f x) X.
Proof.
apply/eq_fset=> x.
rewrite /supp /mkdistr /= domm_mkfmapfp in_fset mem_filter in_fset_filter /=.
by case: insubP=> [? ->|/negbTE ->].
Qed.

Record prob :=
  Prob {pval : {distr T}; _ : mass pval == 1%R}.
Definition prob_of & phant T := prob.
Notation "{ 'prob' T }" := (prob_of (Phant T))
  (at level 0, format "{ 'prob'  T }") : form_scope.
Identity Coercion prob_of_prob : prob_of >-> prob.
Coercion pval : prob >-> distr_of.

Canonical prob_subType := [subType for pval].
Definition prob_eqMixin := [eqMixin of prob by <:].
Canonical prob_eqType := EqType prob prob_eqMixin.
Definition prob_choiceMixin := [choiceMixin of prob by <:].
Canonical prob_choiceType := Eval hnf in ChoiceType prob prob_choiceMixin.
Definition prob_ordMixin := [ordMixin of prob by <:].
Canonical prob_ordType := Eval hnf in OrdType prob prob_ordMixin.

Canonical prob_of_subType := [subType of {prob T}].
Canonical prob_of_eqType  := [eqType  of {prob T}].
Canonical prob_of_choiceType := [choiceType of {prob T}].
Canonical prob_of_ordType := [ordType of {prob T}].

Lemma mkprob_subproof X f :
  (forall x, 0 <= f x) ->
  \sum_(x <- X) f x = 1 ->
  \sum_(x <- supp (mkdistr X f)) mkdistr X f x == 1.
Proof.
move=> pos <-; apply/eqP.
rewrite [RHS](bigID (fun x => 0 < f x)) /=.
have -> : \sum_(x <- X | ~~ (0 < f x)) f x = 0.
  rewrite big1 // => x.
  by case: (Num.Theory.sgrP (f x)) (pos x).
rewrite GRing.addr0 supp_mkdistr val_fset_filter big_filter.
rewrite big_seq_cond [RHS]big_seq_cond.
apply: eq_big=> // x /andP [x_X _].
by rewrite mkdistrE x_X pos.
Qed.

Fact mkprob_key : unit. Proof. exact: tt. Qed.

Definition mkprob X f pos e : {prob T} :=
  locked_with mkprob_key (Prob (@mkprob_subproof X f pos e)).

Lemma mkprobE X f pos e x :
  @mkprob X f pos e x = if x \in X then f x else 0.
Proof.
by rewrite /mkprob unlock /= mkdistrE pos andbT.
Qed.

Definition dirac_def x x' : rat :=
  if x == x' then 1 else 0.

Lemma dirac_subproof1 x x' : 0 <= dirac_def x x'.
Proof. by rewrite /dirac_def; case: eq_op. Qed.

Lemma dirac_subproof2 x : \sum_(x' <- fset1 x) dirac_def x x' = 1.
Proof.
by rewrite /= big_seq1 /dirac_def eqxx.
Qed.

Definition dirac x :=
  mkprob (dirac_subproof1 x) (dirac_subproof2 x).

Lemma diracE x x' : dirac x x' = if x' == x then 1 else 0.
Proof.
rewrite /dirac /dirac_def /= mkprobE in_fset1.
by rewrite eq_sym; case: (x == x').
Qed.

Lemma supp_dirac x : supp (dirac x) = fset1 x.
Proof.
apply/eq_fset=> x'.
by rewrite mem_supp in_fset1 diracE; case: eq_op.
Qed.

Lemma supp_diracP x x' : reflect (x' = x) (x' \in supp (dirac x)).
Proof. rewrite supp_dirac; exact: fset1P. Qed.

Lemma eq_prob (p1 p2 : {prob T}) : p1 =1 p2 <-> p1 = p2.
Proof. by split=> [/eq_distr/val_inj|-> //]. Qed.

Lemma in_eq_probL (p1 p2 : {prob T}) : {in supp p1, p1 =1 p2} -> p1 = p2.
Proof.
move=> e; apply/eq_prob=> x.
case: (boolP (x \in supp p1))=> xP; first exact: e.
rewrite (suppPn xP).
have: \sum_(y <- supp p1) p2 y = 1.
  rewrite -(eqP (valP p1)) /mass /= big_seq [RHS]big_seq.
  by apply/eq_big=> // ? /e ->.
rewrite -(eqP (valP p2)) /mass /= [RHS](bigID (mem (supp p1))) /=.
rewrite -[in RHS]big_filter -val_fset_filter.
have ->: fset_filter (mem (supp p1)) (supp p2) = supp p1.
  apply/eq_fset=> y; rewrite in_fset_filter /=.
  case: (boolP (y \in supp p1))=> //= y_p1.
  by rewrite mem_supp -(e _ y_p1) -mem_supp.
rewrite -[LHS]GRing.addr0 => /GRing.addrI/esym/eqP.
rewrite Num.Theory.psumr_eq0; last by move=> ? _; rewrite distr_ge0.
case: (boolP (x \in supp p2)) => x_p2; last by rewrite (suppPn x_p2).
by move=> /allP/(_ _ x_p2); rewrite xP => /eqP ->.
Qed.

Lemma in_eq_projR (p1 p2 : {prob T}) : {in supp p2, p1 =1 p2} -> p1 = p2.
Proof.
by move=> e; apply/esym/in_eq_probL=> x x_p2; rewrite e.
Qed.

Definition of_dirac (p : {prob T}) : option T :=
  if val (supp p) is [:: x] then Some x
  else None.

Lemma diracK : pcancel dirac of_dirac.
Proof. by move=> x; rewrite /of_dirac supp_dirac /=. Qed.

Lemma of_diracK : ocancel of_dirac dirac.
Proof.
rewrite /of_dirac => p.
case e: (val (supp p))=> [//|x[|//]] /=.
have {}e: supp p = fset1 x by rewrite fset1E -e fsvalK.
move/eqP: (valP p); rewrite /mass e /= big_seq1 => p_x.
apply/in_eq_projR=> y; rewrite e => /fset1P ->.
by rewrite p_x diracE eqxx.
Qed.

End Prob.

Notation "{ 'distr' T }" := (distr_of (Phant T))
  (at level 0, format "{ 'distr'  T }") : form_scope.
Notation "{ 'prob' T }" := (prob_of (Phant T))
  (at level 0, format "{ 'prob'  T }") : form_scope.

Arguments suppPn {_ _ _}.
Arguments dirac {_} x.

Section Sample.

Variables T S : ordType.
Variable (p : {prob T}) (f : T -> {prob S}).
Implicit Types (x : T) (y : S).

Let Y   : {fset S} := \bigcup_(x <- supp p) supp (f x).
Let P y : rat      := \sum_(x <- supp p) p x * f x y.

Lemma sample_subproof1 y : 0 <= P y.
Proof.
apply: Num.Theory.sumr_ge0 => x _.
apply: Num.Theory.mulr_ge0; exact: distr_ge0.
Qed.

Lemma sample_subproof2 : \sum_(y <- Y) P y = 1.
Proof.
rewrite /P exchange_big /= -(eqP (valP p)).
apply/eq_big=> //= x _.
case: (boolP (x \in supp p)); last first.
  by move=> /suppPn ->; apply/big1=> y _; rewrite GRing.mul0r.
rewrite -GRing.mulr_sumr -[RHS]GRing.mulr1 => x_p; congr (_ * _).
rewrite -(eqP (valP (f x))) /=; symmetry; apply/massE.
apply/fsubsetP=> y; rewrite mem_supp => yP.
apply/bigcupP; exists x=> //.
by rewrite mem_supp.
Qed.

Definition sample :=
  mkprob sample_subproof1 sample_subproof2.

Lemma sample_defE0 y : (y \in Y) = (P y != 0).
Proof.
rewrite /P Num.Theory.psumr_eq0 -?has_predC /=; last first.
  move=> x _; apply: Num.Theory.mulr_ge0; exact: distr_ge0.
apply/(sameP bigcupP)/(iffP hasP).
- case=> /= x x_p n0; exists x=> //.
  by move: n0; rewrite GRing.mulf_eq0 negb_or mem_suppN; case/andP.
- case=> /= x; rewrite !mem_suppN => x_p _ y_f.
  by exists x; rewrite 1?mem_suppN // GRing.mulf_neq0.
Qed.

Lemma sampleE y : sample y = P y.
Proof.
rewrite /sample mkprobE sample_defE0.
by case: (P y =P 0)=> [->|].
Qed.

Lemma supp_sample : supp sample = Y.
Proof.
apply/eq_fset=> x.
by rewrite mem_suppN sample_defE0 sampleE.
Qed.

Lemma supp_sampleP y :
  reflect (exists2 x, x \in supp p & y \in supp (f x)) (y \in supp sample).
Proof.
rewrite supp_sample; apply/(iffP bigcupP).
- by case=> ????; eauto.
- by case=> ???; eexists; eauto.
Qed.

End Sample.

Declare Scope prob_scope.
Local Open Scope prob_scope.

Notation "'sample:' x '<-' t1 ';' t2" :=
  (sample t1 (fun x => t2))
  (at level 20, t1 at level 100, t2 at level 200,
   right associativity, format "'[' 'sample:'  x  '<-'  '[' t1 ;  ']' ']' '/' t2 ")
  : prob_scope.

Section SampleProps.

Variables T S : ordType.

Lemma sample_diracL (x : T) (f : T -> {prob S}) : sample (dirac x) f = f x.
Proof.
apply/eq_prob=> y; rewrite sampleE supp_dirac /= big_seq1.
by rewrite mkprobE in_fset1 eqxx /dirac_def eqxx GRing.mul1r.
Qed.

Lemma sample_diracR (p : {prob T}) : sample p dirac = p.
Proof.
apply/eq_prob=> x; rewrite sampleE.
transitivity (\sum_(x' <- supp p) if x == x' then p x' else 0).
  apply/eq_big=> // x' _.
  rewrite diracE /= eq_sym.
  case: eq_op; by rewrite ?GRing.mulr0 ?GRing.mulr1.
rewrite -big_mkcond /= -big_filter -val_fset_filter.
case: (boolP (x \in supp p))=> x_p.
  rewrite (_ : fset_filter _ _ = fset1 x) /= ?big_seq1 //.
  apply/eq_fset=> x'; rewrite in_fset_filter in_fset1 eq_sym.
  by case: (x' =P x)=> [->|].
rewrite (_ : fset_filter _ _ = fset0) /= ?big_nil ?(suppPn x_p) //.
apply/eq_fset=> x'; rewrite in_fset_filter eq_sym.
by case: (x' =P x)=> // ->; rewrite (negbTE x_p).
Qed.

End SampleProps.

Open Scope prob_scope.

Fixpoint map_p T (S : ordType) (f : T -> {prob S}) (xs : seq T) : {prob seq S} :=
  match xs with
  | [::] => dirac [::]
  | x :: xs =>
    sample: y  <- f x;
    sample: ys <- map_p f xs;
    dirac (y :: ys)
  end.

Definition mapim_p (T : ordType) (S : Type) (R : ordType)
  (f : T -> S -> {prob R}) (m : {fmap T -> S}) : {prob {fmap T -> R}} :=
  let do_pair p := sample: y <- f p.1 p.2; dirac (p.1, y) in
  sample: pairs <- map_p do_pair (val m);
  dirac (mkfmap pairs).
