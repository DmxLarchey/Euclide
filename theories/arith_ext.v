(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Arith Lia Utf8.

(** Petite extension de la librairie Arith *)

#[local] Notation lt_0_Sn := Nat.lt_0_succ.

Fact nat_case_0_gt (P : nat → Type) n : P 0 → (0 < n → P n) → P n.
Proof. destruct n; intros H1 H2; auto; apply H2; lia. Qed.

Fact nat_case_0_1_gt (P : nat → Type) n : P 0 → P 1 → (1 < n → P n) → P n.
Proof. destruct n as [ | [ | ] ]; intros ? ? H; auto; apply H; lia. Qed.

Tactic Notation "zero" "or" "more" hyp(i) "as" ident(H) :=
  pattern i; apply nat_case_0_gt; [ | intros H ].

Tactic Notation "zero" "one" "or" "more" hyp(n) "as" ident(H) :=
  pattern n; apply nat_case_0_1_gt; [ | | intros H ].

Fact plus_comm n m : n+m = m+n.
Proof. ring. Qed.

Fact plus_is_one a b : a+b = 1 → a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0.
Proof. lia. Qed.

Fact mult_assoc n m p : n*(m*p) = n*m*p.
Proof. ring. Qed.

Fact mult_comm n m : n*m = m*n.
Proof. ring. Qed.

Fact mult_plus_distr_r n m p : (n+m)*p = n*p+m*p.
Proof. ring. Qed.

Fact mult_minus_distr_r n m p : (n-m)*p = n*p-m*p.
Proof. apply Nat.mul_sub_distr_r. Qed.

Fact mult_is_one a b : a*b = 1 → a = 1 ∧ b = 1.
Proof. revert a b; intros [|[]] [|[]]; simpl; auto; lia. Qed.

Fact mult_cancel k a b : k*a = k*b → 0 < k ∧ a = b ∨ k = 0.
Proof.
   destruct k as [ | k ]; auto.
   intros ?%Nat.mul_cancel_l; lia.
Qed.

Fact mult_eq_cancel x n m : 0 < x → x*n = x*m → n = m.
Proof. intros ? ?%mult_cancel; lia. Qed.

Fact mult_ka_a_cancel k a : k*a = a → 0 < a ∧ k = 1 ∨ a = 0.
Proof.
  intros H.
  apply mult_cancel.
  rewrite <- H at 2; ring.
Qed.

Fact pow_gt_0 x n : 0 < x → 0 < x^n.
Proof.
  unfold lt at 2.
  rewrite <- (Nat.pow_1_l n).
  apply Nat.pow_le_mono_l.
Qed.
