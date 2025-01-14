(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Arith Lia Wellfounded Extraction Utf8.

Require Import measure.

(** Une analyse par cas sur n, spécialisée, 
    avec un contrôle fin du code extrait. *)

Definition zero_or_succ (P : nat → Type) n :
    (n = 0 → P 0)
  → (∀ p, n = S p → P n)
  → P n :=
  match n return (n = _ → _) → (∀p, n = _ → P n) → P n with
  | 0   => λ h0 _, h0 eq_refl
  | S _ => λ _ hS, hS _ eq_refl 
  end.

Extraction Inline zero_or_succ.

Tactic Notation "zero" "or" "succ" hyp(n) "as" ident(x) ident(H) :=
  pattern n; apply zero_or_succ; [ intros H | intros x H ].

#[local] Reserved Notation "x ≺ₑ y" (at level 70, format "x  ≺ₑ  y").

Section euclid_rect.

   (** Rappel des appels récursifs de l'algorithme d'Euclide
       sur les entiers de Peano avec accumulateur 

         (a,0,0)      ~(1)~> terminé
         (0,x,0)      ~(2)~> terminé
         (0,0,y)      ~(3)~> terminé
         (1+a,1+x,0)  ~(4)~> (1,x,a)
         (1+a,0,1+y)  ~(5)~> (1,a,y)
         (a,1+x,1+y)  ~(6)~> (1+a,x,y)

       La relation d'Euclide sur les triplets (a,x,y) modélise
       les sous-appel récursifs de l'algorithme d'Euclide avec
       accumulateur sur les entiers de Peano *)

  Inductive euclid_rel : nat*nat*nat → nat*nat*nat → Prop :=
    | euclid_rel'_ax0 a x :     (1,x,a) ≺ₑ (S a,S x,0)
    | euclid_rel'_a0y a y :     (1,a,y) ≺ₑ (S a,0,S y)
    | euclid_rel'_aSS a x y : (S a,x,y) ≺ₑ (a,S x,S y)
  where "x ≺ₑ y" := (euclid_rel x y).

  Hint Constructors euclid_rel : core.

  Let m '(a,x,y) := a+x+y.

  (* La relation _ ≺ₑ _ est incluse dans une relation bien-fondée *)
  Local Fact euclid_rel_incl_measure p q : p ≺ₑ q → m p < m q.
  Proof. unfold m; destruct 1; lia. Qed.

  (* Donc elle est bien fondée *)
  Local Lemma wf_euclid_rel : well_founded (λ p q, p ≺ₑ q).
  Proof.
    apply wf_incl with (1 := euclid_rel_incl_measure),
          wf_inverse_image, lt_wf.
  Qed.

  Variables (P : nat → nat → nat → Type)
            (H_a00 : ∀ a, P a 0 0)
            (H_0x0 : ∀ x, P 0 x 0)
            (H_00y : ∀ y, P 0 0 y)
            (H_ax0 : ∀ a x, P 1 x a → P (S a) (S x) 0)
            (H_a0y : ∀ a y, P 1 a y → P (S a) 0 (S y))
            (H_axy : ∀ a x y, P (S a) x y → P a (S x) (S y)).

  (* Le récurseur (ou principe d'induction) ad-hoc.
     On l'écrit de manière très détaillée pour un 
     contrôle maximal du code extrait. *)
  Definition euclid_rect a x y : P a x y.
  Proof.
    induction on a x y as euclid_rect wf by wf_euclid_rel.
    revert euclid_rect.
    zero or succ x as x' Hx; zero or succ y as y' Hy.
    + intros _; apply H_a00.
    + zero or succ a as a' Ha; intros euclid_rect.
      * apply H_00y.
      * subst a y; apply H_a0y, euclid_rect; auto.
    + zero or succ a as a' Ha; intros euclid_rect.
      * apply H_0x0.
      * subst a x; apply H_ax0, euclid_rect; auto.
    + intros euclid_rect; subst x y; apply H_axy, euclid_rect; auto.
  Defined.

End euclid_rect.

Extraction Inline euclid_rect.

Section gcd_rect.

  Variables (P : nat → nat → Type)
            (H_n0 : ∀ n, P n 0)
            (H_0n : ∀ n, P 0 n)
            (H_nn : ∀ n, P n n)
            (H_na : ∀ a n, 0 < a → 0 < n → P n a → P (a+n) a)
            (H_an : ∀ a n, 0 < a → 0 < n → P a n → P a (a+n)).

  Hint Resolve Nat.lt_0_succ : core. (*  0 < S _ *)

  (* Ceci est un récurseur spécialisé pour le gcd et bezout
     qui cache l'accumulateur présent dans son implémentation
     via euclid_rect *)
  Definition gcd_rect : ∀ x y, P x y.
  Proof.
    change (∀ x y, (λ a u v, P (a+u) (a+v)) 0 x y).
    apply euclid_rect with (a := 0).
    + intros; rewrite !Nat.add_0_r; auto.
    + apply H_n0.
    + apply H_0n.
    + intros; rewrite Nat.add_0_r; auto.
    + intros; rewrite Nat.add_0_r; auto.
    + intros; now rewrite <- !Nat.add_succ_comm.
  Defined.

End gcd_rect.

Extraction Inline gcd_rect.
