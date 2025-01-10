(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

Require Import Arith Lia Utf8.

Require Import arith_ext divides gcd_rect.

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

(* L'ingrédient essentiel de l'algorithme d'Euclide pour les coefficients de Bezout. *)
Lemma coprime_plus x y : x ⊥ y → y+x ⊥ y.
Proof.
  intros H d H1 H2; apply H; auto with div_db.
  now apply div_plus_equiv in H1.
Qed.

Lemma coprime_plus_rev x y : y+x ⊥ y → x ⊥ y.
Proof.
  intros H d H1 H2; apply H; auto.
  now apply div_plus_equiv.
Qed.

#[global] Hint Resolve coprime_0l coprime_0r coprime_diag coprime_sym 
                       coprime_plus coprime_plus_rev : coprime_db.

Section Bezout.

  Variables (a b : nat).

  (** On prouve une version de l'identité de Bachet-Bezout adaptée
      aux entiers naturels:

        a ⊥ b ↔ ∃ u v u' v', u*a + v*b = 1 + u'*a + v'*b

      qui a une preuve simple qui étend l'algorithme d'Euclide
      pour le calcul du gcd, toujours en style tail-récursif.

      On peut obtenir le résultat plus fort:

        a ⊥ b ↔ ∃ u v, u*a + v*b = 1 + a*b

      avec une preuve plus complexe mais quand même en style
      tail-récursif, voir le fichier bezout_better.v.

      Si on veut généraliser à ∃ u v, u*a + v*b = a⨅b + a⨆b,
      (ou (a⨅b)*(a⨆b) = a*b) il n'est pas sûr que l'on puisse
      procéder avec un algo. tail-rec, mais on a une version
      assez simple dans le fichier bezout_simple.v *)

  Local Lemma Bachet_Bezout_tr x y u1 v1 u1' v1' u2 v2 u2' v2' :
      x ⊥ y
    → u1*a + v1*b = x + u1'*a + v1'*b
    → u2*a + v2*b = y + u2'*a + v2'*b
    → ∃ u v u' v', u*a + v*b = 1 + u'*a + v'*b.
  Proof.
    revert u1 v1 u1' v1' u2 v2 u2' v2'.
    pattern x, y; revert x y; apply gcd_rect.
    + intros n u1 v1 u1' v1' u2 v2 u2' v2' ->%coprime_0r E E'.
      now exists u1,v1,u1',v1'.
    + intros n u1 v1 u1' v1' u2 v2 u2' v2' ->%coprime_0l E E'.
      now exists u2,v2,u2',v2'.
    + intros n u1 v1 u1' v1' u2 v2 u2' v2' ->%coprime_diag E E'.
      now exists u1,v1,u1',v1'.
    + intros c x _ _ loop u1 v1 u1' v1' u2 v2 u2' v2' G E E'.
      apply (loop (u1+u2') (v1+v2') (u1'+u2) (v1'+v2) u2 v2 u2' v2');
        auto with coprime_db.
      rewrite !Nat.mul_add_distr_r; lia.
    + intros c y _ _ loop u1 v1 u1' v1' u2 v2 u2' v2' G E E'.
      apply (loop u1 v1 u1' v1' (u1'+u2) (v1'+v2) (u2'+u1) (v2'+v1));
        auto with coprime_db.
      rewrite !Nat.mul_add_distr_r; lia.
  Qed.

  Theorem Bezout : a ⊥ b ↔ ∃ u v u' v', u*a + v*b = 1 + u'*a + v'*b.
  Proof.
    split.
    + intro; apply (Bachet_Bezout_tr a b 1 0 0 0 0 1 0 0); trivial.
    + intros (u & v & u' & v' & E) d Ha Hb.
      apply div_1r.
      rewrite div_plus_equiv with (a := u'*a+v'*b); auto with div_db.
      rewrite (Nat.add_comm _ 1), Nat.add_assoc, <- E; auto with div_db.
 Qed.

End Bezout.

(* Le lemme du Gauss s'obtient à partir de l'identité de Bezout:
   Si d est premier avec x, et d divise x.y, alors d divise y. *)
Lemma Gauss d x y : d ⊥ x → d∣x*y → d∣y.
Proof.
  intros (u & v & u' & v' & E)%Bezout (q & Hq).
  apply f_equal with (f := λ n, n*y) in E.
  rewrite !mult_plus_distr_r,
       <- !(mult_assoc _ x y),
       <- Hq, Nat.mul_1_l,
       <- Nat.add_assoc,
          (plus_comm y)
    in E.
  apply div_plus_equiv
    with (a := u'*d*y+v'*(q*d));
    auto with div_db.
  rewrite <- E; auto with div_db.
Qed.
