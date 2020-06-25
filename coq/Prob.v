Require Import Coq.Strings.String.
Require Import Coq.Unicode.Utf8.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq
  ssrint rat ssralg ssrnum bigop path.

From extructures Require Import ord fset fmap ffun.

From void Require Import void.

From deriving Require Import deriving.

From RandC Require Import Extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope fset_scope.

Section Prob.

Variable T : ordType.
Implicit Types (x : T) (X : {fset T}) (f : T -> rat).

Record distr := Distr {
  dval :> ffun (fun _ : T => 0 : rat);
  _    :  all (fun x => 0 <= dval x) (supp dval)
}.
Definition distr_of & phant T := distr.
Notation "{ 'distr' T }" := (distr_of (Phant T))
  (at level 0, format "{ 'distr'  T }") : form_scope.
Identity Coercion distr_of_distr : distr_of >-> distr.

Canonical distr_subType  := [subType for dval].
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

Lemma eq_distr d1 d2 : d1 =1 d2 <-> d1 = d2.
Proof.
by split=> [e|-> //]; apply/val_inj/eq_ffun.
Qed.

Lemma distr_ge0 d x : 0 <= d x.
Proof.
case: (boolP (x \in supp d))=> [|/suppPn -> //].
apply/allP: x; exact/(valP d).
Qed.

Definition mass d := \sum_(x <- supp d) d x.

Lemma massE d X :
  fsubset (supp d) X -> mass d = \sum_(x <- X) d x.
Proof.
rewrite /mass => sub.
have -> : supp d = fset_filter (mem (supp d)) X.
  apply/eq_fset=> x; rewrite in_fset_filter /=.
  by case: (boolP (x \in supp d))=> // /(fsubsetP sub) ->.
rewrite val_fset_filter big_filter big_mkcond /=.
by apply/eq_big=> // x _; case: ifPn=> // /suppPn ->.
Qed.

Fact mkdistr_key : unit. Proof. exact: tt. Qed.

Lemma mkdistr_subproof (X : {fset T}) (f : T -> rat) :
  (forall x, x \in X -> 0 <= f x) ->
  let ff := @mkffun _ _ (fun _ => 0) f X in
  all (fun x => 0 <= ff x) (supp ff).
Proof.
move=> /= pos; apply/allP=> x _; rewrite mkffunE.
by case: ifP=> // /pos.
Qed.

Definition mkdistr X f pos :=
  locked_with mkdistr_key
    (Distr (@mkdistr_subproof X f pos)).

Lemma mkdistrE X f pos x :
  @mkdistr X f pos x = if (x \in X) then f x else 0%R.
Proof. by rewrite /mkdistr unlock /= mkffunE. Qed.

Lemma supp_mkdistr X f pos : supp (@mkdistr X f pos) = fset_filter (fun x => f x != 0) X.
Proof.
apply/eq_fset=> x; rewrite mem_supp mkdistrE.
by rewrite -mkffunE -mem_supp supp_mkffun in_fset mem_filter.
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

Lemma mkprob_subproof X f pos :
  \sum_(x <- X) f x = 1 ->
  mass (@mkdistr X f pos) == 1.
Proof.
move=> <-; apply/eqP.
rewrite [RHS](bigID (fun x => f x == 0)) /=.
have -> : \sum_(x <- X | f x == 0) f x = 0.
  by rewrite big1 // => x /eqP.
rewrite GRing.add0r /mass supp_mkdistr val_fset_filter big_filter.
rewrite big_seq_cond [RHS]big_seq_cond.
by apply: eq_big=> // x /andP [x_X _]; rewrite mkdistrE x_X.
Qed.

Fact mkprob_key : unit. Proof. exact: tt. Qed.

Definition mkprob X f pos e : {prob T} :=
  locked_with mkprob_key (Prob (@mkprob_subproof X f pos e)).

Lemma mkprobE X f pos e x :
  @mkprob X f pos e x = if x \in X then f x else 0.
Proof. by rewrite /mkprob unlock /= mkdistrE. Qed.

Definition dirac_def x x' : rat :=
  if x == x' then 1 else 0.

Lemma dirac_subproof1 x x' : x' \in fset1 x -> 0 <= dirac_def x x'.
Proof. by rewrite /dirac_def; case: eq_op. Qed.

Lemma dirac_subproof2 x : \sum_(x' <- fset1 x) dirac_def x x' = 1.
Proof.
by rewrite /= big_seq1 /dirac_def eqxx.
Qed.

Definition dirac x :=
  mkprob (@dirac_subproof1 x) (dirac_subproof2 x).

Lemma diracE x x' : dirac x x' = if x' == x then 1 else 0.
Proof.
rewrite /dirac /dirac_def /= mkprobE in_fset1.
by rewrite eq_sym; case: (x == x').
Qed.

Lemma supp_dirac x : supp (dirac x) = fset1 x.
Proof.
apply/eq_fset=> x'.
by rewrite mem_supp in_fset1 diracE; case: ifP.
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

Arguments dirac {_} x.
Arguments of_dirac {_} p.

Section Sample.

Variables T S : ordType.
Variable (p : {prob T}) (f : T -> {prob S}).
Implicit Types (x : T) (y : S).

Let Y   : {fset S} := \bigcup_(x <- supp p) supp (f x).
Let P y : rat      := \sum_(x <- supp p) p x * f x y.

Lemma sample_subproof1 y : y \in Y -> 0 <= P y.
Proof.
move=> _; apply: Num.Theory.sumr_ge0 => x _.
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
  by move: n0; rewrite GRing.mulf_eq0 negb_or mem_supp; case/andP.
- case=> /= x; rewrite !mem_supp => x_p _ y_f.
  by exists x; rewrite 1?mem_supp // GRing.mulf_neq0.
Qed.

Lemma sampleE y : sample y = P y.
Proof.
rewrite /sample mkprobE sample_defE0.
by case: (P y =P 0)=> [->|].
Qed.

Lemma supp_sample : supp sample = Y.
Proof.
apply/eq_fset=> x.
by rewrite mem_supp sample_defE0 sampleE.
Qed.

Lemma supp_sampleP y :
  reflect (exists2 x, x \in supp p & y \in supp (f x)) (y \in supp sample).
Proof.
rewrite supp_sample; apply/(iffP bigcupP).
- by case=> ????; eauto.
- by case=> ???; eexists; eauto.
Qed.

End Sample.

Arguments supp_sampleP {_ _ _ _ _}.

Declare Scope prob_scope.
Local Open Scope prob_scope.

Notation "'sample:' x '<-' t1 ';' t2" :=
  (sample t1 (fun x => t2))
  (at level 20, t1 at level 100, t2 at level 200,
   right associativity, format "'[' 'sample:'  x  '<-'  '[' t1 ;  ']' ']' '/' t2")
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

Lemma eq_sample (p : {prob T}) (f g : T -> {prob S}) :
  f =1 g -> sample p f = sample p g.
Proof.
move=> efg; apply/eq_prob=> y.
by rewrite !sampleE; apply/eq_big=> // x _; rewrite efg.
Qed.

Lemma eq_in_sample (p : {prob T}) (f g : T -> {prob S}) :
  {in supp p, f =1 g} -> sample p f = sample p g.
Proof.
move=> efg; apply/eq_prob=> y.
rewrite !sampleE big_seq [in RHS]big_seq.
by apply/eq_big=> // x /efg ->.
Qed.

End SampleProps.

Lemma sampleA (T S R : ordType) p (f : T -> {prob S}) (g : S -> {prob R}) :
  (sample: y <- (sample: x <- p; f x); g y) =
  (sample: x <- p; sample: y <- f x; g y).
Proof.
apply/eq_prob=> z.
transitivity (\sum_(y <- supp (sample: x <- p; f x))
                \sum_(x <- supp p) p x * f x y * g y z).
  rewrite sampleE; apply/eq_big=> // y _.
  by rewrite sampleE GRing.mulr_suml.
rewrite sampleE exchange_big /= big_seq [RHS]big_seq.
apply/eq_big=> // x px.
transitivity (\sum_(y <- supp (sample: x <- p; f x))
                 p x * (f x y * g y z)).
  by apply/eq_big=> ? // _; rewrite GRing.mulrA.
rewrite <- GRing.mulr_sumr; congr *%R; rewrite sampleE.
have /fsetIidPl <-: fsubset (supp (f x)) (supp (sample: x <- p; f x)).
  apply/fsubsetP=> y fxy; rewrite supp_sample.
  by apply/bigcupP; exists x.
rewrite /fsetI val_fset_filter big_filter [RHS]big_mkcond /=.
apply/eq_big=> // y _; rewrite mem_supp.
by case: eqP=> //= ->; rewrite GRing.mul0r.
Qed.

Open Scope prob_scope.

Fixpoint map_p T (S : ordType) (f : T -> {prob S}) (xs : seq T) : {prob seq S} :=
  match xs with
  | [::] => dirac [::]
  | x :: xs =>
    sample: y  <- f x;
    sample: ys <- map_p f xs;
    dirac (y :: ys)
  end.

Lemma eq_map_p T (S : ordType) (f g : T -> {prob S}) :
  f =1 g -> map_p f =1 map_p g.
Proof. by move=> fg; elim=> //= x xs IH; rewrite fg IH. Qed.

Lemma map_p_dirac (T : ordType) (xs : seq T) : map_p dirac xs = dirac xs.
Proof.
elim: xs=> //= x xs IH.
by rewrite sample_diracL IH sample_diracL.
Qed.

Lemma map_p_comp T S (R : ordType) (f : T -> S) (g : S -> {prob R}) xs :
  map_p g [seq f x | x <- xs] = map_p (g \o f) xs.
Proof. by elim: xs=> //= x xs ->. Qed.

Lemma supp_map_p T (S : ordType) (f : T -> {prob S}) xs ys :
  ys \in supp (map_p f xs) =
  all2 (fun x y => y \in supp (f x)) xs ys.
Proof.
elim: xs ys=> [|x xs IH] [|y ys] /=.
- by rewrite supp_dirac.
- by rewrite supp_dirac.
- case: supp_sampleP=> //=.
  by case=> y' y'P /supp_sampleP [ys' _ /supp_diracP].
- rewrite -IH; apply/(sameP supp_sampleP)/(iffP andP).
  + case=> [yP ysP]; exists y=> //.
    apply/supp_sampleP; exists ys=> //.
    by apply/supp_diracP.
  + by case=> [y' y'P /supp_sampleP [ys' ys'P /supp_diracP [-> ->]]].
Qed.

Section MapMapProb.

Variable T : ordType.

Definition mapim_p (S : Type) (R : ordType)
  (f : T -> S -> {prob R}) (m : {fmap T -> S}) : {prob {fmap T -> R}} :=
  let do_pair p := sample: y <- f p.1 p.2; dirac (p.1, y) in
  sample: pairs <- map_p do_pair (val m);
  dirac (mkfmap pairs).

Lemma eq_mapim_p (S : Type) (R : ordType)
  (f g : T -> S -> {prob R}) :
  f =2 g -> mapim_p f =1 mapim_p g.
Proof.
move=> fg m; rewrite /mapim_p.
by under eq_map_p => p do rewrite fg.
Qed.

Lemma mapim_p_dirac (S : ordType) (m : {fmap T -> S}) :
  mapim_p (fun _ => dirac) m = dirac m.
Proof.
rewrite /mapim_p.
under eq_map_p => p do rewrite sample_diracL -surjective_pairing.
by rewrite map_p_dirac sample_diracL fmvalK.
Qed.

Lemma mapim_p_comp (S R U : ordType)
  (g : T -> R -> {prob U}) (f : T -> S -> R) m :
  mapim_p g (mapim f m) =
  mapim_p (fun x y => g x (f x y)) m.
Proof. by rewrite /mapim_p /= map_p_comp. Qed.

Fact mapm_p_key : unit. Proof. exact: tt. Qed.

Definition mapm_p (S : Type) (R : ordType) (f : S -> {prob R}) :=
  locked_with mapm_p_key (mapim_p (fun (x : T) => f)).

Lemma eq_mapm_p (S : Type) (R : ordType) (f g : S -> {prob R}) :
  f =1 g -> mapm_p f =1 mapm_p g.
Proof.
rewrite /mapm_p !unlock.
by move=> e; apply/eq_mapim_p=> ??; eauto.
Qed.

Lemma mapm_p_dirac (S : ordType) (m : {fmap T -> S}) :
  mapm_p dirac m = dirac m.
Proof. rewrite /mapm_p !unlock; exact/mapim_p_dirac. Qed.

Lemma mapm_p_comp (S R U : ordType) (g : R -> {prob U}) (f : S -> R) m :
  mapm_p g (mapm f m) = mapm_p (g \o f) m.
Proof. rewrite /mapm_p !unlock; exact/mapim_p_comp. Qed.

Lemma supp_mapm_p (S R : ordType) (f : S -> {prob R}) m1 m2 :
  m2 \in supp (mapm_p f m1) =
  (domm m1 == domm m2) &&
  all (fun x => match m1 x, m2 x with
                | Some y, Some z => z \in supp (f y)
                | _, _ => true
                end) (domm m1).
Proof.
rewrite /mapm_p unlock /mapim_p.
apply/(sameP supp_sampleP)/(iffP andP).
- case=> /eqP edomm ecodomm; exists (val m2); last first.
    by apply/supp_diracP; rewrite fmvalK.
  have /= esize: size (val m1) = size (val m2).
    move/(congr1 (size \o val)): edomm.
    by rewrite /= !val_domm !size_map => ->.
  rewrite supp_map_p all2E esize eqxx /=.
  apply/allP=> /= - xyz /(nthP xyz) [i].
  rewrite size_zip -esize minnn=> isize.
  case: xyz=> [[x1 y] [x2 z]]; rewrite nth_zip //=; case=> e1 e2.
  have e1' : nth x1 (domm m1) i = x1.
    by rewrite val_domm (nth_map (x1, y)) // e1.
  have e2' : nth x2 (domm m2) i = x2.
    by rewrite val_domm (nth_map (x2, z)) -?esize // e2.
  have ex: x1 = x2.
    rewrite -e1' -e2' -edomm; apply/set_nth_default.
    by rewrite val_domm size_map.
  move: x1 ex e1 e2 {e1' e2'}=> {x2} x <- e1 e2.
  have {}e1: m1 x = Some y.
    by apply/getmP; rewrite -e1; apply/mem_nth.
  have {}e2: m2 x = Some z.
    by apply/getmP; rewrite -e2; apply/mem_nth; rewrite -esize.
  have xP: x \in domm m1 by rewrite mem_domm e1.
  move/allP/(_ _ xP): ecodomm; rewrite e1 e2=> yz.
  by apply/supp_sampleP; exists z; rewrite // supp_dirac in_fset1 eqxx.
- case=> {}m2 m2P /supp_diracP ->.
  move: m2P; rewrite supp_map_p all2E; case/andP=> /eqP esize ecodomm.
  have edomm : unzip1 m1 = unzip1 m2.
    move: m2 esize ecodomm; rewrite /=.
    elim: {m1} (val m1)=> [|[x1 y] m1 IH] [|[x2 z] m2] //= [esize].
    case/andP=> /supp_sampleP [{}z _ /supp_diracP [-> _]] ecodomm.
    congr cons; exact: IH.
  have m2_sorted: mkfmap m2 = m2 :> seq _.
    apply/mkfmapK; rewrite -edomm; exact: (valP m1).
  have {}edomm : domm m1 = domm (mkfmap m2).
    by apply/val_inj; rewrite /= !val_domm m2_sorted.
  split; first by rewrite edomm.
  move: esize ecodomm; rewrite -m2_sorted.
  move: (mkfmap m2) edomm=> {m2_sorted} {}m2 /= edomm esize ecodomm.
  apply/allP=> x /dommP [y yP]; rewrite yP fmvalK.
  have /dommP [z zP]: x \in domm m2 by rewrite -edomm mem_domm yP.
  rewrite zP.
  case/getmP/(nthP (x, y)): (yP)=> /= i isize ei1.
  have ei1domm : nth x (domm m1) i = x.
    by rewrite val_domm (nth_map (x, y)) // ei1.
  have ei2: nth (x, z) m2 i = (x, z).
    move: zP; rewrite -{1} ei1domm edomm.
    rewrite (getm_nth (x, z)) -?esize //; case=> {2}<-.
    move: ei1domm; rewrite edomm val_domm (nth_map (x, z)) -?esize //.
    by move=> e; rewrite -[X in _ = (X, _)]e [LHS]surjective_pairing.
  have inzip : nth ((x, y), (x, z)) (zip m1 m2) i = ((x, y), (x, z)).
    by rewrite nth_zip // ei1 ei2.
  have {}inzip: ((x, y), (x, z)) \in zip m1 m2.
    by rewrite -inzip; apply/mem_nth; rewrite size_zip -esize minnn.
  move/allP/(_ _ inzip): ecodomm; rewrite inE /=.
  by case/supp_sampleP=> ?? /supp_diracP [->].
Qed.

Lemma supp_mapm_pP (S R : ordType) (f : S -> {prob R}) m1 m2 :
  reflect (domm m1 = domm m2 /\
           forall x y z, m1 x = Some y -> m2 x = Some z -> z \in supp (f y))
          (m2 \in supp (mapm_p f m1)).
Proof.
rewrite supp_mapm_p; apply/(iffP andP).
- case=> /eqP edomm ecodomm; split=> // x y z yP zP.
  have xP: x \in domm m1 by rewrite mem_domm yP.
  by move/allP/(_ _ xP): ecodomm; rewrite yP zP.
- case=> edomm ecodomm; split; first by rewrite edomm.
  apply/allP=> x xP; case/dommP: (xP)=> y yP.
  move: (xP); rewrite edomm; case/dommP=> z zP.
  rewrite yP zP; apply: ecodomm yP zP.
Qed.

End MapMapProb.
