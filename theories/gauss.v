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
    proposée par Euclide et est présentée ici:

     https://www.imo.universite-paris-saclay.fr/~daniel.perrin/CAPES/arithmetique/lemmeEuclide.pdf

    mais en fait on peut directement montrer sa
    généralisation, le lemme de Gauss:

       d ⊥ x → d∣x.y → d∣y

    avec la même méthode.

    A noter que nous avons du changer la définition de la
    notion de "représentation la plus petite" en gardant
    seulement la minimalité du dénominateur, afin de
    pouvoir démontrer plus facilement l'existence
    d'une plus petite représentation, qui n'est pas
    expliquée dans la référence ci-dessus, ni semble-t-il
    par Euclide lui-même (voir discussion plus loin).

    Nous supposons que l'auteur s'appuie sur le principe
    de minimisation des entiers naturels: toute propriété P
    sur les entiers, vraie pour au moins un entier, est
    vraie pour un plus petit entier. Ce principe n'est
    démontrable dans une théorie intuitionniste telle 
    que Coq que pour les propriétés décidables, càd
    vérifiant ∀n, P n ∨ ¬ P n. Il se trouve que c'est
    le cas de la propriété utilisée pour construire
    la plus petite représentation.

    Il est discutable que cette preuve soit plus
    simple qu'obtenir Gausse via Bezout. *)

(* La division Euclidienne de x par d>0 càd
     p et r tels que x=p.d+r et r<d 
   est unique. *)
Proposition eucl_div_uniq d p r q s :
    0 < d
  → p*d+r = q*d+s
  → r < d
  → s < d 
  → p = q ∧ r = s.
Proof.
  intros H1 H2 H3 H4.
  destruct (lt_eq_lt_dec p q)
    as [ [ C | ] | C ].
  + (* la distance entre r et s est < d
       donc ne peut compenser (q-p)d *)
    exfalso.
    replace q with (1+p+(q-p-1)) in H2 by lia.
    rewrite mult_plus_distr_r in H2; simpl in H2.
    revert H2; generalize ((q-p-1)*d); lia.
  + (* comme p=q, il s'en suit r=s *)
    subst; lia.
  + (* la distance entre r et s est < d
       donc ne peut compenser (p-q)d *)
    exfalso.
    replace p with (1+q+(p-q-1)) in H2 by lia.
    rewrite mult_plus_distr_r in H2; simpl in H2.
    revert H2; generalize ((p-q-1)*d); lia.
Qed.

(* Une représentation de a/b = x/y où b≤y vérifie aussi a≤x.
   C'est une remarque et on n'a pas besoin de ce résultat. *)
Remark small_denom__num a b x y : 0 < b → x*b = y*a → b ≤ y → a ≤ x.
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

(* Une plus petite représentation a/b minimise 
   le dénominateur. A noter qu'elle minimise aussi
   le numérateur d'après la remarque small_denom__num.
   Mais en fait, on n'a pas besoin de cette propriété
   du numérateur. *)
Definition smallest_repr a b :=
  0 < b ∧ ∀ x y, 0 < y → x*b = y*a → b ≤ y.

(* Pour trouver une plus petite représentation de x/y,
   on cherche dans l'ordre, une représentation de 
   la forme ?/1, puis ?/2, puis ?/3 ..., et enfin, 
   à défaut, x/y. On minimise donc "uniquement" le
   dénominateur, ce qui a pour effet de bord de
   minimiser aussi le numérateur d'après la
   remarque small_denom__num. *)
Proposition find_smallest_repr x y :
  0 < y → ∃ a b, x*b = y*a ∧ smallest_repr a b.
Proof.
  intros Hy.
  destruct find_first 
    with (P := λ b, 0 < b ∧ y∣x*b)
         (n := y)
    as (b & H1 & (H2 & a & Ha) & H3).
  + intros i _;
      destruct (lt_dec 0 i);
      destruct (div_wdec y (x*i));
      tauto.
  + auto with div_db.
  + exists a, b; split;[|split]; try lia.
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
    intros (Hb & H) x y Hy E;
    generalize (H _ _ Hy E); intros G2.
  + rewrite Nat.mul_0_r in E.
    exists y.
    assert (b=1) as ->; try lia.
    generalize (H 0 1); lia.
  + destruct (eucl_dev _ Ha x) as [ p r Hr Ep ].
    destruct (eucl_dev _ Hb y) as [ q s Hs Eq ].
    assert (p*(a*b) + r*b = q*(a*b) + s*a) as G.
    1:{ rewrite (mult_comm a) at 2.
        now rewrite !mult_assoc,
                 <- !mult_plus_distr_r,
                 <- Ep, <- Eq. }
    apply eucl_div_uniq in G as (<- & H1).
    * revert Hs Eq H1.
      zero or more s as Hs'; intros Hs Eq H1.
      - exists p; assert (r=0) as ->; lia.
      - apply H in H1; lia. 
    * lia.
    * apply Nat.mul_lt_mono_pos_r; auto.
    * rewrite (mult_comm a).
      apply Nat.mul_lt_mono_pos_r; auto.
Qed.

(** Pour le résultat de caractérisation suivant, Euclide
    nous semble faire une erreur de raisonnement, si
    toutefois son oeuvre est correctement transcrite ici:

    http://aleph0.clarku.edu/~djoyce/java/elements/bookVII/propVII21.html

    En effet, il y est dit que si a ⊥ b n'est pas
    une plus petite représentation alors il en existe
    une inférieure, x/y = a/b avec x≤a et y≤b. 
    Mais c'est un principe de minimisation
    "sur deux entiers simultanément", et un tel 
    principe serait incorrect en général: 

      en effet P (a,b) := a+b=2 fournit un contre-exemple
      car P est vraie sur les paires (2,0),(1,1) et (0,2)
      mais ces paires sont toutes incomparables.

    Toutefois le résultat reste vrai car on peut trouver une 
    plus petite représentation en minimisant uniquement le 
    dénominateur. Le numérateur suit d'après la remarque 
    small_denom__num. Voir aussi find_smallest_repr. *)

(* Nous évitons le problème en n'utilisant uniquement
   le dénominateur pour comparer les représentations. *)
Corollary coprime_smallest_repr a b :
     0 < b → a ⊥ b ↔ smallest_repr a b.
Proof.
  intros Hb; split.
  + (* Constructivement, il n'est pas si trivial
       qu'il existe une plus petite représentation. *)
    intros Hab.
    destruct (find_smallest_repr a b) as (u & v & H3 & H4); auto.
    destruct (smallest_repr_divides _ _ H4 _ _ Hb H3) as (e & G1 & G2).
    assert (e = 1) as ->.
    * apply Hab; subst; auto with div_db.
    * subst; now rewrite !Nat.mul_1_r.
  + (* la réciproque est plus simple *)
    intros (_ & H) d (e1 & H1) (e2 & H2).
    assert (b ≤ e2) as H3.
    1:{ apply (H e1 e2).
        * revert H2; zero or more e2 as H3; lia.
        * subst a b; ring. }
    revert H2 H3.
    zero one or more d as Hd; try lia.
    rewrite mult_comm.
    replace d with (2+(d-2)) by lia.
    rewrite !mult_plus_distr_r; lia.
Qed.

(* La référence ne mentionne pas qu'en fait on
   peut même démontrer le lemme de Gauss, plus
   général que le lemme d'Euclide. *)
Lemma Gauss d x y : d ⊥ x → d∣x*y → d∣y.
Proof.
  zero or more d as Hd.
  + intros ->%coprime_0l.
    now rewrite Nat.mul_1_l.
  + intros Hxd%coprime_sym (u & Hu).
    generalize (proj1 (coprime_smallest_repr x _ Hd) Hxd); intros H.
    rewrite (mult_comm x) in Hu.
    zero or more y as Hy; auto with div_db.
    destruct (smallest_repr_divides _ _ H _ _ Hy Hu)
      as (e & G1 & <-); auto with div_db.
Qed.

