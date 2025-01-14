(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Arith Lia Euclid Utf8.

Require Import arith_ext divides bounded_choice prime.

(** La démonstration du lemme d'Euclide suit la preuve
    proposée par Euclide et présentée ici:

     https://www.imo.universite-paris-saclay.fr/~daniel.perrin/CAPES/arithmetique/lemmeEuclide.pdf

    A noter que j'ai du changer la définition de la
    notion de "représentation la plus petite" en gardant
    seulement la minimalité du dénominateur, afin de
    pouvoir démontrer plus facilement l'existence 
    d'une plus petite représentation, qui n'est même
    pas expliquée dans la référence ci-dessus.

    Il est discutable que cette preuve soit plus
    simple qu'obtenir Euclide via Bezout puis Gauss. *)

(* La division Euclidienne de x par d>0 càd
     p et r tels que x=p.d+r et r<d 
   est unique. *)
Fact eucl_div_uniq d p r q s :
    0 < d
  → p*d+r = q*d+s 
  → r < d
  → s < d 
  → p = q ∧ r = s.
Proof.
  intros H1 H2 H3 H4.
  destruct (lt_eq_lt_dec p q)
    as [ [ C | <- ] | C ].
  + exfalso.
    replace q with (1+p+(q-p-1)) in H2 by lia.
    rewrite mult_plus_distr_r in H2; simpl in H2.
    revert H2; generalize ((q-p-1)*d); intro; lia.
  + lia.
  + exfalso.
    replace p with (1+q+(p-q-1)) in H2 by lia.
    rewrite mult_plus_distr_r in H2; simpl in H2.
    revert H2; generalize ((p-q-1)*d); intro; lia.
Qed.

(* Une représentation de a/b = x/y où b≤y vérifie aussi a≤x *)
Fact small_denom__num a b x y : 0 < b → x*b = y*a → b ≤ y → a ≤ x.
Proof.
  intros Hb E Hy.
  destruct (le_lt_dec a x) as [ | C ]; auto.
  exfalso.
  rewrite (mult_comm y) in E.
  replace a with (S x+(a-S x)) in E by lia.
  rewrite mult_plus_distr_r in E; simpl in E.
  revert E; generalize ((a-S x)*y); intro.
  generalize (Nat.mul_le_mono_l _ _ x Hy); lia.
Qed.

(* Une plus petite représentation a/b minimise le dénominateur *)
Definition smallest_repr a b :=
  0 < b ∧ ∀ x y, 0 < y → x*b = y*a → b ≤ y.

(* Pour trouver une plus petite représentation de x/y,
   on essaye dans l'ordre d'en trouver une de la forme
   ?/1, puis ?/2, puis ?/3 ..., puis à défaut ?/y. *)
Proposition find_smallest_repr x y : 
  0 < y → ∃ a b, x*b = y*a ∧ smallest_repr a b.
Proof.
  intros Hy.
  destruct find_first 
    with (P := λ b, 0 < b ∧ y∣x*b)
         (n := y)
    as (b & H1 & (H2 & a & Ha) & H3).
  + intros i _; destruct (lt_dec 0 i); destruct (div_wdec y (x*i)); tauto.
  + auto with div_db.
  + exists a, b; split; try lia.
    split; auto.
    intros u v Hv E.
    destruct (le_lt_dec b v) as [ | C]; auto.
    destruct (H3 _ C); split; auto.
    exists u.
    apply mult_eq_cancel with b; auto.
    rewrite !mult_assoc, (mult_comm _ x), 
            (mult_comm b), <- Ha, E; ring.
Qed.

(* Si a/b est une plus petite représentation et a/b = x/y
   alors il existe e tel que a.e = x et b.e = y *)
Lemma smallest_repr_divides a b :
    smallest_repr a b
  → ∀ x y, 0 < y → x*b = y*a → ∃e, a*e = x ∧ b*e = y.
Proof.
  zero or more a as Ha;
    intros (Hb & H) x y Hy E.
  + generalize (H _ _ Hy E); intros G2.
    rewrite Nat.mul_0_r in E.
    assert (b <= 1) by (apply (H 0 1); auto).
    assert (b=1) as -> by lia.
    exists y; lia.
  + generalize (H _ _ Hy E); intros G2.
    destruct (eucl_dev _ Ha x) as [ p r Hr Ep ].
    destruct (eucl_dev _ Hb y) as [ q s Hs Eq ].
    assert (p*(a*b) + r*b = q*(a*b) + s*a) as G.
    1:{ rewrite (mult_comm a) at 2. 
        rewrite !mult_assoc, <- !mult_plus_distr_r.
        now rewrite <- Ep, <- Eq. }
    apply eucl_div_uniq in G as (<- & H1).
    * revert Hs Eq H1.
      zero or more s as Hs'; intros Hs Eq H1.
      - assert (r=0) as -> by lia.
        exists p; lia.
      - apply H in H1; lia. 
    * lia.
    * apply Nat.mul_lt_mono_pos_r; auto.
    * rewrite (mult_comm a).
      apply Nat.mul_lt_mono_pos_r; auto.
Qed.

Fact coprime__smallest_repr a b :
    a ⊥ b 
  → 0 < b
  → smallest_repr a b.
Proof.
  intros H1 H2.
  (* Il n'y pas trivial qu'il existe une plus petite représentation *)
  destruct (find_smallest_repr a b) as (u & v & H3 & H4); auto.
  destruct (smallest_repr_divides _ _ H4 _ _ H2 H3) as (e & G1 & G2).
  assert (e = 1) as ->.
  1: apply H1; subst; auto with div_db.
  rewrite Nat.mul_1_r in G1, G2; now subst.
Qed.

Lemma Euclid p x y : prime p → p∣x*y → p∣x ∨ p∣y.
Proof.
  intros Hp H.
  destruct (prime__div_or_coprime p Hp x) as [ | C ].
  1: now left.
  generalize (prime_gt_0 _ Hp); intros Hp'.
  destruct H as (u & Hu).
  apply coprime_sym in C.
  generalize (coprime__smallest_repr _ _ C Hp'); intros H.
  rewrite (mult_comm x) in Hu.
  zero or more y as Hy.
  1: right; auto with div_db.
  destruct (smallest_repr_divides _ _ H _ _ Hy Hu)
    as (e & G1 & G2).
  subst; auto with div_db.
Qed.
