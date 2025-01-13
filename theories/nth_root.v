(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import Arith Lia Utf8.

Require Import arith_ext divides bounded_choice gauss.

(** Notion de nombre entier premier *)

#[global] Create HintDb prime_db.

(* p est premier si p≠1 et n'a pas d'autre diviseur que 1 et p. *)
Definition prime p := p≠1 ∧ ∀d, d∣p → d=1 ∨ d=p.

(* Si p est premier et ne divise pas x, alors il est premier avec x. *)
Lemma prime_no_div_coprime p : prime p → ∀x, ¬ p∣x → p ⊥ x.
Proof. intros H ? ? ? [ -> | -> ]%H; now trivial. Qed.

(* si p est premier, soit il divise x, soit il est premier avec x. *)
Lemma prime__div_or_coprime p : prime p → ∀x, p∣x ∨ p ⊥ x.
Proof.
  intros ? x.
  destruct (div_wdec p x); auto.
  right; now apply prime_no_div_coprime.
Qed.

(* Le lemme d'Euclide s'obtient à partir du lemme de Gauss :
   si p premier divise x.y alors p divise x ou p divise y. *)
Lemma Euclid p x y : prime p → p∣x*y → p∣x ∨ p∣y.
Proof.
  intros Hp H.
  destruct (prime__div_or_coprime p Hp x).
  + now left.
  + right; now apply (Gauss p x y).
Qed.

Lemma Euclid_pow p q n : prime p → p∣q^n → p∣q.
Proof.
  intros Hp; induction n as [ | n IHn ]; simpl.
  + intros ->%div_1r; auto with div_db.
  + intros []%Euclid; eauto.
Qed.

Section checking_primality.

  Remark zero_not_prime : ¬ prime 0.
  Proof.
    intros [ H' H ].
    specialize (H 2).
    destruct H as [ H | H ].
    + auto with div_db.
    + easy.
    + easy.
  Qed.

  Remark one_not_prime : ¬ prime 1.
  Proof. now  intros [ [] ]. Qed.

  (** Pour démontrer qu'un nombre n'est pas premier,
     il suffit d'en donner une factorisation non triviale.
     Ce n'est pas possible pour 0 ou 1 mais pour les autres
     ça marche bien. *)

  Remark product_not_prime p q : 1 < p -> 1 < q -> ¬ prime (p*q).
  Proof.
    intros Hp Hq [ ? H].
    destruct (H p); try lia; auto with div_db.
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

(* Ni 0 ni 1 ne sont premiers donc *)
Fact prime__ge_2 p : prime p → 2 ≤ p.
Proof.
  destruct p; intros [ H1 H2 ]; try lia.
  destruct (H2 2); lia || auto with div_db.
Qed.

#[global] Hint Resolve zero_not_prime one_not_prime four_not_prime 
                       two_prime three_prime five_prime
                       prime__ge_2 : prime_db.

(* A partir du lemme d'Euclide *)
Lemma two_divides_square k : 2∣k*k → 2∣k.
Proof. intros []%Euclid; auto with prime_db. Qed.

(* Une preuve qu'aucun rationel ne peut-être la
   racine carrée de 2: √2 est irrationel.

   A noter que l'on démontrer ici qu'il n'existe
   pas de fraction p/q "normalisée" (càd avec p ⊥ q)
   dont le carré soit 2. *)
Theorem root_2_not_rational p q : p ⊥ q → 2*q*q = p*p → False.
Proof.
  intros Hpq H.
  assert (2∣p) as Hp
    by (apply two_divides_square; rewrite <- H; auto with div_db).
  case Hp; intros p' Hp'.
  rewrite mult_comm in Hp'.
  rewrite <- Hp', <- !mult_assoc in H.
  apply mult_eq_cancel in H; [ | lia ].
  assert (2∣q) as Hq
    by (apply two_divides_square; rewrite H; auto with div_db).
  (* 2 divise p et q, et p ⊥ q donc 2 = 1 ce qui est absurde. *)
  generalize (Hpq _ Hp Hq).
  discriminate.
Qed.

(** Si on veut montrer par exemple que √12 n'est pas
    rationnel, la technique précédente ne fonctionne
    pas parce que 12∣p² n'implique pas 12∣p.
    En effet 12 = 2².3 n'est pas un nombre premier
    et ainsi on a pex 12∣6² mais 12 ne divise pas 6.

    De même, si veut éviter de supposer que la fraction
    est normalisée, ce qui implique de calculer le gcd,
    alors on doit procéder autrement.

    Donc il faut généraliser le résultat et l'on va
    démontrer : dⁿ∣kⁿ → d∣k (quand n>0). *)

(** Mais d'abord, on a besoin d'isoler des facteurs 
    premiers dans les nombres entiers. On montre qu'on
    peut toujours trouver un facteur premier d'un nombre
    (autre que 0 ou 1). 

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
Lemma prime_factor d : 1 < d → ∃ p q, prime p ∧ d = p*q ∧ q < d.
Proof.
  intros Hd.
  destruct find_first with (P := λ i, 1 < i ∧ i∣d) (n := d) 
    as (p & H1 & (H2 & q & Hq) & H4).
  + intros i ?; destruct (div_wdec i d); destruct (lt_dec 1 i); tauto.
  + auto with div_db.
  + exists p, q; split; split; try lia.
    * intros e He.
      destruct div_le with (1 := He); try lia.
      revert He H; case 01n e as He'; intros He [H|H]%le_lt_eq_dec; auto.
      - apply div_0l in He; lia.
      - destruct (H4 _ H ); split; subst; auto with div_db.
    * rewrite <- Hq.
      replace q with (q*1) at 1 by ring.
      apply Nat.mul_lt_mono_pos_l; lia.
Qed.

(* On utilise aussi la forme positive ci-dessous, sans contrainte
   a priori sur d, et le complément q dans p dans d divise strictement d. *)
Corollary prime_factor' d : d = 0 ∨ d = 1 ∨ ∃ p e, prime p ∧ d = p*e ∧ e⇂d.
Proof.
  case 01n d as Hd; auto; do 2 right.
  destruct prime_factor with (1 := Hd) as (p & e & H1 & H2 & H3).
  exists p, e; repeat (split; auto).
  + exists p; auto.
  + rewrite H2; intros H.
    rewrite mult_comm in H.
    replace e with (e*1) in H at 2 by lia.
    apply div_cancel in H as [ ->%div_1r | -> ]; lia.
Qed.

(** Voici le résultat fondamental pour démontrer 
    l'irrationalité de ⁿ√k si k n'est pas déjà 
    de la forme k = rⁿ avec r entier:

      si dⁿ∣kⁿ alors soit d∣k, soit n=0 *)

(* A noter qu'ici on ne suppose pas que d soit premier.
   En effet, quand d est premier, il suffit d'appliquer
   Euclid_pow (si n>0).
   Dans le cas général où d n'est pas forcément premier,
   cette preuve procède par induction sur d en utilisant
   l'ordre bien-fondé de divisibilité stricte.
   Ensuite, on isole un facteur premier de d afin de
   pouvoir appliquer Euclid_pow. *)
Theorem div_pow_simplify n d k : d^n∣k^n → d∣k ∨ n=0.
Proof.
  intros Hk.
  (* On élimine le cas n=0 *)
  case 0n n as Hn; [ auto | left ].
  (* Reste le cas 0<n, et on procède par induction sur d
     en utilisant _⇂_ comme relation bien fondée,
     après avoir généralisés k et Hd (qui dépend de k) *)
  induction d as [ d IHd ] in k, Hk |- * using sdiv_induction.
  (* Soit p un factor premier de d *)
  destruct (prime_factor' d) as [ -> | [ -> | (p & e & H1 & H2 & H3) ] ].
  + (* cas d = 0 *)
    rewrite Nat.pow_0_l in Hk; try lia.
    apply div_0l, Nat.pow_eq_0 in Hk as ->; try lia; auto with div_db.
  + (* cas d = 1 *)
    auto with div_db.
  + (* cas d > 1, alors d = p.e avec p premier et e⇂d *)
    (* comme p∣d∣dⁿ∣kⁿ, alors p∣k par Euclid_pow *)
    assert (p∣k) as (r & Hr).
    1:{ apply Euclid_pow with n; trivial.
        apply div_trans with (2 := Hk),
              div_trans with d;
          subst; auto with div_db. }
    (* donc k=p.r et donc dⁿ∣kⁿ donne pⁿeⁿ∣pⁿrⁿ *) 
    rewrite mult_comm in Hr.
    rewrite -> H2, <- Hr, !Nat.pow_mul_l in Hk.
    (* comme pⁿeⁿ∣pⁿrⁿ, on déduit eⁿ∣rⁿ *)
    apply div_cancel in Hk
      as [ Hk | []%Nat.pow_eq_0_iff ];
      [ | apply prime__ge_2 in H1; lia ].
    (* par hypothèse d'induction, de eⁿ∣rⁿ 
       on déduit e|r *)
    generalize (IHd _ H3 _ Hk).
    (* et donc d=p.e divise k=p.r *)
    subst d k; auto with div_db.
Qed.

(** Par définition, ⁿ√k est rationel, c-à-d k a une
    racine n-ième qui est rationelle, si il existe
    une fraction (entière) p/q (avec q≠0) telle que
    k = (p/q)ⁿ, ou encore, k.qⁿ = pⁿ si on veut une
    représentation de cette équation qui évite la
    notion de nombre rationel. *)

Definition nth_root_rational n k := ∃ p q, q ≠ 0 ∧ k*q^n = p^n.
Definition nth_root_irrational n k := ¬ nth_root_rational n k.

(* Si k = (p/q)ⁿ (avec q≠0) alors k = rⁿ où r est entier
   Attention, dans le cas où n=0 alors x⁰ = 1 dans les
   entiers naturels, et en particulier 0⁰ = 1. *)
Theorem nth_root_rational__is_pow n k : nth_root_rational n k → ∃r, k = r^n.
Proof.
  intros (p & q & Hq & H).
  rewrite (mult_comm k) in H.
  destruct (div_pow_simplify n q p) as [ (m & Hm) | H1 ]; try lia.
  + rewrite <- H; auto with div_db. 
  + exists m.
    replace (p^n) with (q^n*m^n) in H.
    * apply mult_eq_cancel in H; auto.
      apply pow_gt_0; lia.
    * rewrite <- Hm, Nat.pow_mul_l; ring.
  + subst; exists 1; simpl in *; lia.
Qed.

(* √2 est irrationel car 2 ≠ rⁿ (avec r entier) *)
Corollary square_root_two_not_rational : nth_root_irrational 2 2.
Proof.
  intros (r & ?)%nth_root_rational__is_pow.
  (* 2 = r², on distingue r=0, r=1, r=2+_ *)
  destruct r as [|[]]; simpl in *; lia.
Qed.

(* Plus généralement, si on veut étudier les racines ⁿ√_,
   pour facilement démontrer que k ≠ rⁿ (avec r entier)
   si on utilise l'encadrement iⁿ < k < (1+i)ⁿ entre deux
   puissances successives. *)
Lemma not_pow_by_witness n k : (∃i, i^n < k < (1+i)^n) → ¬ ∃r, k = r^n.
Proof.
  intros (i & H1 & H2); revert H1 H2.
  case 0n i as Hi.
  + destruct n; simpl; try lia.
    rewrite Nat.pow_1_l; lia.
  + intros H1 H2 (x & H3).
    destruct (le_lt_dec x i) as [ H4 | H4 ];
      apply Nat.pow_le_mono_l with (c := n) in H4; simpl in *; lia.
Qed.

Theorem irrationality_criteria n k : (∃i, i^n < k < (1+i)^n) → nth_root_irrational n k.
Proof. intros ? H%nth_root_rational__is_pow%not_pow_by_witness; auto. Qed.

(* On écrit une tactique qui combine nth_root_rational__is_pow et
   not_pow_by_witness, à laquelle on fournit l'encradement
   iⁿ < ... < (1+i)ⁿ.

   On pourrait éventuellement chercher cet encadrement de manière
   automatique. *)
Tactic Notation "solve" "irrational" "with" constr(x) :=
  intros; apply irrationality_criteria; exists x; simpl; lia.

(* ²√2 irrationelle car 1² < 2 < 2² *)
Goal nth_root_irrational 2 2.
Proof. solve irrational with 1. Qed.

(* ³√7 irrationelle car 1³ < 7 < 2³ *)
Goal nth_root_irrational 3 7.
Proof. solve irrational with 1. Qed.

(* ⁵√132 irrationelle car 2⁵ < 132 < 3⁵ *)
Goal nth_root_irrational 5 132.
Proof. solve irrational with 2. Qed.

(* ²√255 irrationelle car 15² < 255 < 16² *)
Goal nth_root_irrational 2 255.
Proof. solve irrational with 15. Qed.

(* ³√n irrationelle pour n ∈ ]27,64[ *)
Goal ∀n, 27 < n < 64 → nth_root_irrational 3 n.
Proof. solve irrational with 3. Qed.

(* ⁵√n irrationel pour n ∈ ]32,243[ *)
Goal ∀n, 32 < n < 243 → nth_root_irrational 5 n.
Proof. solve irrational with 2. Qed.

(** Petite parenthèse : les nombres premiers sont en quantité
    non-bornée, c-à-d infinie. Pour démontrer celà, on peut
    par exemple utiliser la fonction factorielle, 
    fact n = 1*...*n *)

Goal fact 0 = 1.
Proof. reflexivity. Qed.

Fact fact_S n : fact (S n) = (S n)*fact n.
Proof. reflexivity. Qed.

(* Tous les nombres 1..n divisent fact n *)
Fact fact_div n d : 0 < d → d ≤ n → d∣fact n.
Proof.
  intros H; induction 1.
  + destruct d; [ lia | ].
    rewrite fact_S; auto with div_db.
  + rewrite fact_S; auto with div_db.
Qed.

(* Les nombres premiers sont en quantité non-bornée,
   c-à-d il n'y a pas de majorant pour les nombres 
   premiers.

   En effet, dans les facteurs premiers de 1+fact n,
   il y a forcément un premier plus grand que n. *)
Theorem prime_unbounded n : ∃p, prime p ∧ n < p.
Proof.
  (* On choisit un facteur premier p de 1+fact n*)
  destruct (prime_factor (1+fact n))
    as (p & q & H1 & H2 & _);
    [ generalize (fact_neq_0 n); lia | ].
  (* alors p est forcément plus grand que n *)
  exists p; split; auto.
  destruct (le_lt_dec p n) as [ H3 | ]; auto.
  (* En effet, si p ≤ n, alors on a p divise fact n *)
  apply fact_div in H3;
    [ | apply prime__ge_2 in H1; lia ].
  (* mais p divise fact n+1 *) 
  assert (p∣fact n+1) as C
    by (exists q; lia).
  (* donc p divise 1, absurde *)
  apply div_plus_equiv, div_1r in C; auto.
  apply prime__ge_2 in H1; lia.
Qed.

(** Fin de la parentèse sur le quantité infinie de 
    nombres premiers. *)
