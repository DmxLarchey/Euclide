(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Arith Lia Utf8.

Require Import arith_ext divides bounded_choice.

(** Notation et base d'astuces *)

#[global] Reserved Notation "x ⊥ y" (at level 70, no associativity, format "x  ⊥  y").
#[global] Create HintDb coprime_db.

(** Notion d'entiers premiers entre eux *)

(* x et y sont premiers entre eux si leur seul diviseur commun est 1. *)
Definition coprime x y := ∀d, d∣x → d∣y → d=1.
Infix "⊥" := coprime.

Fact coprime_sym x y : x ⊥ y → y ⊥ x.  Proof. intros H ? ? ?; now apply H. Qed.
Fact coprime_0r x :    x ⊥ 0 → x = 1.  Proof. intros H; apply H; auto with div_db. Qed.
Fact coprime_0l y :    0 ⊥ y → y = 1.  Proof. intros H; apply H; auto with div_db. Qed.
Fact coprime_diag x :  x ⊥ x → x = 1.  Proof. intros H; apply H; auto with div_db. Qed.

#[global] Hint Resolve coprime_0l coprime_0r coprime_diag coprime_sym : coprime_db.

(** Notion de nombre entier premier *)

#[global] Create HintDb prime_db.

(* p est premier si p≠1 et n'a pas d'autre diviseur que 1 et p. *)
Definition prime p := p≠1 ∧ ∀d, d∣p → d=1 ∨ d=p.

Fact zero_not_prime : ¬ prime 0.
Proof.
  intros [ _ H ].
  specialize (H 2).
  destruct H as [ H | H ].
  + auto with div_db.
  + easy.
  + easy.
Qed.

Fact one_not_prime : ¬ prime 1.
Proof. now intros [ [] ]. Qed.

Fact prime_gt_0 p : prime p → 0 < p.
Proof.
  zero or more p as Hp; auto.
  now intros ?%zero_not_prime.
Qed.

(* Ni 0 ni 1 ne sont premiers donc *)
Fact prime_ge_2 p : prime p → 2 ≤ p.
Proof.
  destruct p; intros [ H1 H2 ]; try lia.
  destruct (H2 2); lia || auto with div_db.
Qed.

#[global] Hint Resolve zero_not_prime one_not_prime
                       prime_gt_0 prime_ge_2 : prime_db.

(* Si p est premier et ne divise pas x, alors il est premier avec x. *)
Lemma prime_no_div_coprime p : prime p → ∀x, ¬ p∣x → p ⊥ x.
Proof.
  (* intros H ? ? ? [ -> | -> ]%H; now trivial. *)
  intros Hp x C d Hdp H.
  apply Hp in Hdp.
  destruct Hdp as [ -> | -> ].
  + trivial.
  + contradict C.
    trivial.
Qed.

(* si p est premier, soit il divise x, soit il est premier avec x. *)
Lemma prime__div_or_coprime p : prime p → ∀x, p∣x ∨ p ⊥ x.
Proof.
  intros ? x.
  destruct (div_wdec p x).
  + left.
    trivial.
  + right.
    apply prime_no_div_coprime.
    * trivial.
    * trivial.
Qed.

Section checking_primality.

  (** Pour démontrer qu'un nombre n'est pas premier,
     il suffit d'en donner une factorisation non triviale.
     Ce n'est pas possible pour 0 ou 1 mais pour les autres
     ça marche bien. *)

  Remark product_not_prime a b : 1 < a → 1 < b → ¬ prime (a*b).
  Proof.
    intros Ha Hb [ ? H].
    destruct (H a); try lia; auto with div_db.
    symmetry in H1; rewrite mult_comm in H1.
    apply mult_ka_a_cancel in H1; lia.
  Qed.

  Remark four_not_prime : ¬ prime 4.
  Proof. apply (product_not_prime 2 2); lia. Qed.

  Remark forty_five_not_prime : ¬ prime 45.
  Proof. apply (product_not_prime 5 9); lia. Qed.

  (** Ci-dessous, pour montrer que p n'est pas premier
      on montre que ni 0, ni 2, ni 3 ..., ni p-1 ne
      divisent p, ce qui est inefficace si p est grand.

      De toutes façons, démontrer qu'un nombre est premier
      est un problème plus complexe mais toutefois important
      en pratique. Même si il est dans la classe P(olynomiale),
      on utilise plutôt des algorithmes approximatifs
      qui sont assez efficaces pour tester la primalité
      avec une faible proportion de faux-positifs. *)

  Ltac destruct_n d n :=
    match n with
    | 0   => idtac
    | S ?n => destruct d as [ | d ]; [ | destruct_n d n ]
    end.
 
  Tactic Notation "analyse" constr(n) "times" "as" ident(d) := intro d; destruct_n d n.

  Remark two_prime : prime 2.
  Proof.
    split.
    + easy.
    + analyse 1 times as d; intros H.
      * now apply div_0l in H.
      * apply div_le in H.
        lia.
  Qed.

  Remark three_prime : prime 3.
  Proof.
    split.
    + easy.
    + analyse 3 times as d; intros H; auto.
      * now apply div_0l in H.
      * destruct H as (k & Hk); lia.
      * apply div_le in H; lia.
  Qed.

  Remark five_prime : prime 5.
  Proof.
    split; try easy.
    analyse 5 times as d; intros H; auto.
    5: apply div_le in H; lia.
    1-4: destruct H as (k & Hl); lia.
  Qed.

End checking_primality.

#[global] Hint Resolve two_prime three_prime 
                       four_not_prime five_prime : prime_db.

(** On montre qu'on peut toujours trouver un facteur premier 
    d'un nombre entier autre que 0 ou 1.

    A noter que la factorization des entiers est un problème
    complexe et on ne connait pas d'algorithme "vraiment" plus
    efficace que la recherche exhaustive effectuée ci-dessous.
    Par "vraiment", on entend ici non-exponentiel.
    La complexité théorique de la factorisation d'un entier
    reste un problème ouvert (P ou NP ?), mais d'importance
    pratique très grande dans la mesure où le chiffrement
    assymétrique RSA est fondé sur la difficulté de la
    factorisation de semi-premiers, càd des produits de
    deux nombres premiers de grande taille, pex 250 chiffres
    décimaux est le record actuel (Wikipedia). *)

(* On peut trouver un facteur premier de tout nombre d>1.
   En effet, par "recherche exhaustive" dans ]1,d] sur la
   condition λ i, i∣d. Comme n lui-même satisfait cette
   condition, il existe un plus petit diviseur de n dans
   ]1,n], qui est alors un facteur premier de n. *) 
Lemma prime_factor d : 1 < d → ∃ p e, prime p ∧ d = p*e ∧ e < d.
Proof.
  intros Hd.
  destruct find_first with (P := λ i, 1 < i ∧ i∣d) (n := d) 
    as (p & H1 & (H2 & e & He) & H4).
  + intros i ?; destruct (div_wdec i d); destruct (lt_dec 1 i); tauto.
  + auto with div_db.
  + exists p, e; split; split; try lia.
    * intros f Hf.
      destruct div_le with (1 := Hf); try lia.
      revert Hf H.
      zero one or more f as Hf';
        intros Hf [H|H]%le_lt_eq_dec; auto.
      - apply div_0l in Hf; lia.
      - destruct (H4 _ H ); split; subst; auto with div_db.
    * rewrite <- He.
      replace e with (e*1) at 1 by ring.
      apply Nat.mul_lt_mono_pos_l; lia.
Qed.

(** Petite parenthèse : les nombres premiers sont en quantité
    non-bornée, c-à-d infinie. Pour démontrer celà, on peut
    par exemple utiliser la fonction factorielle, 
    fact m = 1*...*m *)

Goal fact 0 = 1.
Proof. simpl. trivial. Qed.

Fact fact_S m : fact (S m) = (S m)*fact m.
Proof. simpl. trivial. Qed.

(* Tous les nombres 1..m divisent fact m *)
Fact fact_div m d : 0 < d → d ≤ m → d∣fact m.
Proof.
  intros H; induction 1.
  + destruct d; [ lia | ].
    rewrite fact_S; auto with div_db.
  + rewrite fact_S; auto with div_db.
Qed.

(* Les nombres premiers sont en quantité non-bornée,
   c-à-d il n'y a pas de majorant pour les nombres
   premiers.

   En effet, dans les facteurs premiers de 1+fact m,
   il y a forcément un premier plus grand que m. *)
Theorem prime_unbounded m : ∃p, prime p ∧ m < p.
Proof.
  (* On choisit un facteur premier p de 1+fact m*)
  destruct (prime_factor (1+fact m))
    as (p & e & H1 & H2 & _);
    [ generalize (fact_neq_0 m); lia | ].
  (* alors p est forcément plus grand que m *)
  exists p; split; auto.
  destruct (le_lt_dec p m) as [ H3 | ]; auto.
  (* En effet, si p ≤ m, alors on a p divise fact m *)
  apply fact_div in H3;
    [ | apply prime_ge_2 in H1; lia ].
  (* mais p divise fact m+1 *) 
  assert (p∣fact m+1) as C
    by (exists e; lia).
  (* donc p divise 1, absurde *)
  apply div_plus_equiv, div_1r in C; auto.
  apply prime_ge_2 in H1; lia.
Qed.

(** Fin de la parentèse sur le quantité infinie de 
    nombres premiers. *)


