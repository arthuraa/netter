From mathcomp Require Import
  ssreflect ssrfun ssrbool ssrnat eqtype seq choice fintype path
  ssrint rat.

From extructures Require Import ord fset fmap ffun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.

(* Consolidate this stuff in extructures. *)

Lemma val_fset_filter (T : ordType) (P : T -> bool) (X : {fset T}) :
  fset_filter P X = filter P X :> seq T.
Proof.
apply: (eq_sorted (@Ord.lt_trans T)).
- move=> x y /andP [/Ord.ltW xy /Ord.ltW yx].
  by apply: Ord.anti_leq; rewrite xy.
- rewrite /fset_filter /fset unlock /=.
  exact: FSet.fset_subproof.
- rewrite sorted_filter ?valP //.
  exact: Ord.lt_trans.
rewrite uniq_perm ?filter_uniq ?uniq_fset //.
by move=> x; rewrite /= in_fset_filter mem_filter.
Qed.

Lemma val_domm (T : ordType) (S : Type) (m : {fmap T -> S}) :
  domm m = unzip1 m :> seq _.
Proof.
apply: (eq_sorted (@Ord.lt_trans T)).
- move=> x y /andP [/Ord.ltW xy /Ord.ltW yx].
  by apply: Ord.anti_leq; rewrite xy.
- exact: valP.
- exact: (valP m).
rewrite uniq_perm // ?uniq_fset //.
  apply: sorted_uniq.
  - exact: (@Ord.lt_trans T).
  - exact: Ord.ltxx.
  - exact: (valP m).
by move=> x; rewrite in_fset.
Qed.

Lemma fmvalK (T : ordType) (S : Type) : cancel val (@mkfmap T S).
Proof.
by move=> /= m; apply/eq_fmap=> x; rewrite mkfmapE.
Qed.

Lemma mapim_map (T : ordType) (S R : Type) (f : S -> R) (m : {fmap T -> S}) :
  mapim (fun=> f) m = mapm f m.
Proof. by []. Qed.

Lemma mkfmapK (T : ordType) (S : Type) (kvs : seq (T * S)) :
  sorted Ord.lt (unzip1 kvs) ->
  mkfmap kvs = kvs :> seq (T * S).
Proof.
elim: kvs=> [|[k v] kvs IH]=> //= kvs_sorted.
rewrite IH ?(path_sorted kvs_sorted) //.
case: kvs kvs_sorted {IH} => [|[k' v'] kvs] //=.
by case/andP=> ->.
Qed.

Lemma getm_nth (T : ordType) (S : Type) p (m : {fmap T -> S}) i :
  i < size m ->
  m (nth p.1 (domm m) i) = Some (nth p m i).2.
Proof.
rewrite val_domm /getm; move: (valP m); rewrite /=.
elim: (val m) i=> [//|[/= k v] kv IH] [|i] /= kv_sorted.
  by rewrite eqxx.
rewrite ltnS=> isize; rewrite (IH _ (path_sorted kv_sorted) isize).
case: eqP=> // kP; have kkv: k \in unzip1 kv.
  by rewrite -kP; apply/mem_nth; rewrite size_map.
move/(order_path_min (@Ord.lt_trans T))/allP/(_ _ kkv): kv_sorted.
by rewrite Ord.ltxx.
Qed.

Arguments bigcupP {_ _ _ _ _ _}.
Arguments mkfmap {_ _}.
Arguments suppPn {_ _ _ _ _}.

Axiom int_ordMixin : Ord.mixin_of int.
Canonical int_ordType := Eval hnf in OrdType int int_ordMixin.

Definition rat_ordMixin := [ordMixin of rat by <:].
Canonical rat_ordType := Eval hnf in OrdType rat rat_ordMixin.

Section FilterMap.

Variables T : ordType.
Variables S R : Type.

Definition filter_map (f : T -> S -> option R) (m : {fmap T -> S}) : {fmap T -> R} :=
  mkfmapfp (fun x => obind (f x) (m x)) (domm m).

Lemma filter_mapE f m x : filter_map f m x = obind (f x) (m x).
Proof.
by rewrite /filter_map mkfmapfpE mem_domm; case: (m x).
Qed.

Lemma mapimK (f : T -> R -> S) (g : T -> S -> option R) :
  (forall x y, g x (f x y) = Some y) ->
  cancel (mapim f) (filter_map g).
Proof.
move=> fK m; apply/eq_fmap=> x.
by rewrite filter_mapE mapimE; case: (m x)=> //= z.
Qed.

End FilterMap.

Lemma mapm_mkfmapf (T : ordType) (S R : Type) (f : S -> R) (g : T -> S)
  (X : {fset T}) : mapm f (mkfmapf g X) = mkfmapf (f \o g) X.
Proof.
by apply/eq_fmap=> x; rewrite !mapmE !mkfmapfE /=; case: ifP.
Qed.

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

Definition mkffunm (T : ordType) (S : eqType) (def : T -> S) (m : {fmap T -> S}) : ffun def :=
  mkffun (fun x => odflt (def x) (m x)) (domm m).

Lemma mkffunmE T S def m x :
  @mkffunm T S def m x = odflt (def x) (m x).
Proof.
by rewrite /mkffunm mkffunE mem_domm; case: (m x).
Qed.

Arguments fdisjointP {_ _ _}.
