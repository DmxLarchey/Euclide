(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import Arith Lia Utf8.

Require Import arith_ext divides bounded_choice prime gauss.

(* Le lemme d'Euclide s'obtient à partir du lemme de Gauss :
   si p premier divise x.y alors p divise x ou p divise y. *)
Lemma Euclid p x y : prime p → p∣x*y → p∣x ∨ p∣y.
Proof.
  intros Hp H.
  destruct (prime__div_or_coprime _ Hp x).
  + left.
    trivial.
  + right.
    apply (Gauss p x y).
    * trivial.
    * trivial.
Qed.

(* Conséquence direct du lemme d'Euclide sur les diviseurs premiers de kⁿ *)
Lemma Euclid_pow p k n : prime p → p∣k^n → p∣k.
Proof.
  intros Hp; induction n as [ | n IHn ]; simpl.
  + intros ->%div_1r; auto with div_db.
  + intros []%Euclid; eauto.
Qed.

(* Le cas particulier d'Euclide pour p∣k² 
   permet la preuve d'irrationalité de √2 *)
Lemma two_divides_square k : 2∣k*k → 2∣k.
Proof. intros []%Euclid; auto with prime_db. Qed.

(* Une preuve qu'aucun rationel ne peut-être la
   racine carrée de 2: √2 est irrationel.

   A noter que l'on démontrer ici qu'il n'existe
   pas de fraction a/b "normalisée" (càd avec a ⊥ b)
   dont le carré soit 2. *)
Theorem root_2_not_rational a b : a ⊥ b → 2*b*b = a*a → False.
Proof.
  intros Hab H.
  assert (2∣a) as Ha
    by (apply two_divides_square; rewrite <- H; auto with div_db).
  case Ha; intros a' Ha'.
  rewrite mult_comm in Ha'.
  rewrite <- Ha', <- !mult_assoc in H.
  apply mult_eq_cancel in H; [ | lia ].
  assert (2∣b) as Hb
    by (apply two_divides_square; rewrite H; auto with div_db).
  (* 2 divise a et b, et a ⊥ b donc 2 = 1 ce qui est absurde. *)
  generalize (Hab _ Ha Hb).
  discriminate.
Qed.

(** Si on veut montrer par exemple que √12 n'est pas
    rationnel, la technique précédente ne fonctionne
    pas parce que 12∣a² n'implique pas 12∣a.
    En effet 12 = 2².3 n'est pas un nombre premier
    et ainsi on a pex 12∣6² mais 12 ne divise pas 6.

    De même, si veut éviter de supposer que la fraction
    est normalisée, ce qui implique de calculer le gcd,
    alors on doit procéder autrement.

    Donc il faut généraliser le résultat et l'on va
    démontrer : dⁿ∣kⁿ → d∣k (quand n>0).

    Mais d'abord on présente une forme positive et
    adaptée de la recherche d'un facteur premier dans
    un entier. *)

(* On utilise aussi la forme positive de prime_factor ci-dessous, sans contrainte
   a priori sur d, et le complément e de p dans d divise strictement d. *)
Proposition prime_factor' d : d = 0 ∨ d = 1 ∨ ∃ p e, prime p ∧ d = p*e ∧ e⇂d.
Proof.
  zero one or more d as Hd; auto; do 2 right.
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
  zero or more n as Hn; [ auto | left ].
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
      [ | apply prime_ge_2 in H1; lia ].
    (* par hypothèse d'induction, de eⁿ∣rⁿ 
       on déduit e|r *)
    generalize (IHd _ H3 _ Hk).
    (* et donc d=p.e divise k=p.r *)
    subst d k; auto with div_db.
Qed.

(** Par définition, ⁿ√k est rationel, c-à-d k a une
    racine n-ième qui est rationelle, si il existe
    une fraction (entière) a/b (avec b≠0) telle que
    k = (a/b)ⁿ, ou encore, k.bⁿ = aⁿ si on veut une
    représentation de cette équation qui évite la
    notion de nombre rationel. *)

Definition nth_root_rational n k := ∃ a b, b ≠ 0 ∧ k*b^n = a^n.
Definition nth_root_irrational n k := ¬ nth_root_rational n k.

(* Si k = (a/b)ⁿ (avec b≠0) alors k = rⁿ où r est entier
   Attention, dans le cas où n=0 alors x⁰ = 1 dans les
   entiers naturels, et en particulier 0⁰ = 1. *)
Theorem nth_root_rational__is_pow n k : nth_root_rational n k → ∃r, k = r^n.
Proof.
  intros (a & b & Hb & H).
  rewrite (mult_comm k) in H.
  destruct (div_pow_simplify n b a) as [ (m & Hm) | H1 ]; try lia.
  + rewrite <- H; auto with div_db. 
  + exists m.
    replace (a^n) with (b^n*m^n) in H.
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
  zero or more i as Hi.
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

(* ³√x irrationelle pour x ∈ ]27,64[ *)
Goal ∀x, 27 < x < 64 → nth_root_irrational 3 x.
Proof. solve irrational with 3. Qed.

(* ⁵√x irrationel pour x ∈ ]32,243[ *)
Goal ∀x, 32 < x < 243 → nth_root_irrational 5 x.
Proof. solve irrational with 2. Qed.
