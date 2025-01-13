(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Arith Lia Utf8.

#[local] Hint Resolve Nat.lt_0_succ PeanoNat.lt_S_n : core.

(** Le theorème du choix borné cherche la première occurence
    de P dans l'interval [0,n[:
    si pour tout i∈[0,n[ on a soit P(i), soit Q(i)
    alors
    - soit il existe i∈[0,n[ avec P(i), et Q(j) pour tout j∈[0,i[
    - soit Q(j) pour tout j∈[0,n[ *)

Theorem bounded_choice (P Q : nat → Prop) n :
        (∀i, i < n → P i ∨ Q i)
      → (∃i, i < n ∧ P i ∧ ∀j, j < i → Q j)
      ∨ (∀i, i < n → Q i).
Proof.
  induction n as [ | n IHn ] in P, Q |- *; intros HPQ.
  + right; now intros ? ?%Nat.nlt_0_r.
  + destruct (HPQ 0) as [ H | H ]; auto.
    * left; exists 0; split; [ | split ]; auto.
      now intros ? ?%Nat.nlt_0_r.
    * destruct (IHn (λ n, P (S n)) (λ n, Q (S n))) as [ (i & H1 & H2 & H3) | H1 ].
      - intros; apply HPQ; now rewrite <- Nat.succ_lt_mono.
      - left; exists (S i); split; [ | split ]; auto.
        ++ now rewrite <- Nat.succ_lt_mono.
        ++ intros [|] ?; auto; apply H3.
      - right; intros [] ?; auto; apply H1.
Qed.

(** Si P est satisfait à l'entier n, et décidable sur
    l'interval [0,n[ alors il existe une première valeur m
    pour laquelle P est satisfait dans l'interval [0,n]. *)

Corollary find_first (P : nat → Prop) n :
        (∀i, i < n → P i ∨ ¬ P i)
      → P n
      → ∃m, m ≤ n ∧ P m ∧ ∀j, j < m → ¬ P j.
Proof.
  intros H1 H2.
  destruct bounded_choice
    with (P := P) (Q := fun i => ~ P i) (n := S n)
    as [ (m & G1 & G2 & G3) | C ].
  + intros i ?.
    destruct (eq_nat_dec i n) as [ -> | ]; auto.
    apply H1; lia.
  + exists m; split; auto; lia.
  + destruct (C n); auto; lia.
Qed. 
