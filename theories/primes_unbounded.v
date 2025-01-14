(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Arith Lia Utf8.

Require Import divides prime.

(** Petite parenthèse: les nombres premiers sont en quantité
    non-bornée, c-à-d infinie. Pour démontrer celà, on peut
    par exemple utiliser la fonction factorielle, 
    fact m = 1*...*m *)

Fact fact_O : fact 0 = 1.
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

(* Les nombres premiers n'ont pas de majorant, donc
   sont en quantité infinie, constructivement.
   En effet, les facteurs premiers de 1+fact m,
   sont plus grands que m et donc il y en a au 
   moins un plus grand que m. *)
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

