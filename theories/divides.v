(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq Require Import Arith Lia Euclid Utf8.

Require Import arith_ext.

(** Notations réservées pour la divisibilité (d∣n), et la divisibilité stricte (d⇂n) *)

#[global] Reserved Notation "d ∣ n" (at level 70, no associativity, format "d ∣ n").
#[global] Reserved Notation "d ⇂ n" (at level 70, no associativity, format "d ⇂ n").

(** Base de donnée "d'astuces", càd de résultats qui contribuent à la recherche 
    automatisée de preuves via les tactiques auto et eauto. Elle est remplie
    au fur et à mesure. *)

#[global] Create HintDb div_db.

(** Notion de divisibilité et de divisibilité stricte *)

(* "d divise n" si n est multiple de d. *)
Definition div d n := ∃q, q*d = n.
Notation "d ∣ n" := (div d n).

(* "d divise n strictement", càd, d divise n mais n ne divise pas d. *)
Definition sdiv d n := d∣n ∧ ¬ n∣d.
Notation "d ⇂ n" := (sdiv d n).

(** Quelques faits simples sur la divisibilité. *)

Fact div_refl a : a∣a.            Proof. exists 1; ring. Qed.
Fact div_0r a :   a∣0.            Proof. exists 0; lia. Qed.
Fact div_1l a :   1∣a.            Proof. exists a; lia. Qed.
Fact div_0l a :   0∣a → a = 0.    Proof. intros []; lia. Qed.
Fact div_1r a  :  a∣1 → a = 1.    Proof. now intros (? & []%mult_is_one). Qed.
Fact div_mult_left a b : a∣a*b.   Proof. exists b; ring. Qed.
Fact div_mult_right a b : b∣a*b.  Proof. exists a; ring. Qed.

Fact div_mult p q a b : p∣a → q∣b → p*q∣a*b.
Proof. intros (x & <-) (y & <-); exists (x*y); ring. Qed.

Fact div_trans a b c : a∣b → b∣c → a∣c.
Proof. intros (? & <-) (? & <-); rewrite mult_assoc; eexists; eauto. Qed.

(* Un peu plus compliqué car on utilise mult_cancel:
       k.a = k.b → 0 < k ∧ a = b ∨ k = 0
   sous la forme
       (u.v).b = 1.b → u = v = 1 ∨ b = 0 *)
Fact div_antisym a b : a∣b → b∣a → a = b.
Proof.
  intros (u & Hu) (v & <-).
  rewrite mult_assoc in Hu.
  apply mult_ka_a_cancel in Hu 
    as [ (_ &(->&->)%mult_is_one) | -> ]; lia.
Qed.

(* On commence à remplir la base div_db *)
#[global] Hint Resolve div_0l div_0r div_1l div_1r
                       div_mult_left div_mult_right
                       div_refl div_antisym div_trans
                       div_mult : div_db.

(** Les tactiques automatiques (e)auto associées
    à la base div_db permet de résoudre les 
    buts suivants automatiquement. *)

Fact div_mult_l a b c : c∣b → c∣a*b.
Proof. info_eauto with div_db. Qed.

Fact div_mult_r a b c : c∣a → c∣a*b.
Proof. eauto with div_db. Qed. 

Fact div_mult2_l a b c : a∣b → c*a∣c*b.
Proof. auto with div_db. Qed.

Fact div_mult2_r a b c : a∣b → a*c∣b*c.
Proof. auto with div_db. Qed.

(* On a aussi besoin de mult_cancel. *)
Fact div_cancel a b g : g*a∣g*b → a∣b ∨ g = 0.
Proof.
  intros (k & Hk).
  rewrite mult_assoc, (mult_comm _ g), <- mult_assoc in Hk.
  apply mult_cancel in Hk as [ [ _ <- ] | ]; auto with div_db.
Qed.

(* Une autre forme du même résultat. *)
Fact div_cancel' a b g : 0 < g → g*a∣g*b → a∣b.
Proof. intros ? []%div_cancel; auto; lia. Qed.

#[global] Hint Resolve div_mult_l div_mult_r
                       div_mult2_l div_mult2_r 
                       div_cancel div_cancel'
                     : div_db.

Fact div_plus d a b : d∣a → d∣b → d∣a+b.
Proof. intros (x & <-) (y & <-); exists (x+y); ring. Qed.

Fact div_minus d a b : d∣a → d∣b → d∣a-b.
Proof. intros (x & <-) (y & <-); exists (x-y); rewrite mult_minus_distr_r; lia. Qed.

#[global] Hint Resolve div_plus div_minus : div_db.

Fact div_plus_equiv d a b : d∣a → d∣b ↔ d∣a+b.
Proof. 
  intros Hx; split; auto with div_db.
  intro; replace b with ((a+b)-a) by lia.
  auto with div_db.
Qed.

(* n^a = n*...*n répété a fois *)
Fact le_div_pow n a b : a ≤ b → n^a∣n^b.
Proof. induction 1; simpl; auto with div_db. Qed.

Fact div_pos_pow n k : 0 < k → n∣n^k.
Proof. intros H; destruct k; simpl; auto with div_db || lia. Qed.

Fact div_div_pow d n k : d∣n → d^k∣n^k.
Proof. induction k; simpl; auto with div_db. Qed.

#[global] Hint Resolve le_div_pow div_pos_pow div_div_pow : div_db.

(** Liens entre divisibilité et ordre naturel sur les entiers. *)

(* Divisibilité vs. inférieur ou égal. *)
Fact div_le a b : a∣b → a ≤ b ∨ b = 0.
Proof. intros [[]]; lia. Qed.

(* Divisibilité stricte vs. strictement inférieur. *)
Fact sdiv_lt a b : a⇂b → a < b ∨ b = 0.
Proof.
  intros [ []%div_le G ]; auto.
  destruct (eq_nat_dec a b) as [ <- | ].
  + contradict G; auto with div_db.
  + lia.
Qed.

(** On démontre que l'on peut "décider" la propriété i∣d
    c'est à dire, soit obtenir une preuve de i∣d, soit
    une preuve du contraire: ¬i∣d, quels que soient i et d.

    En logique intuitioniste, le "tiers exclu" ne s'applique
    pas et donc on n'a pas forcément P ∨ ¬P pour n'importe
    quelle proposition P.
    Seules les propositions P (logiquement) décidables satisfont
    cette propriété, ce qui est le cas de la divisibilité. *)

(* Pour décider si i∣d, on utilise la division Euclidienne
   dans le cas où i>0. On écrit d = q.i+r avec r < i. Si
   r = 0 alors i∣d et si r > 0 alors ¬ i∣d.
   Dans le cas où i=0, le résultat dépend juste de 
   l'alternative d=0 ou d>0. *)
Lemma div_wdec i d : i∣d ∨ ¬i∣d.
Proof.
  zero or more i as Hi.
  + (* i=0, on distingue d=0 et d>0 *)
    zero or more d as Hd.
    * left; auto with div_db.
    * right; intros ->%div_0l; lia.
  + (* i>0, on peut réaliser la division euclienne de d par i *)
    destruct (eucl_dev i Hi d) as [ q r H1 H2 ].
    (* d = q.i + r et r < i *)
    (* on distingue r = 0 et r > 0 *)
    revert H1 H2; zero or more r as Hr; intros H1 ->.
    * (* r = 0 *)
      left; auto with div_db.
    * (* 0 < r < i *)
      right; intros C.
      apply div_plus_equiv in C; auto with div_db.
      apply div_le in C; lia.
Qed.

(** On s'intéresse maintenant aux principes d'induction bien-fondée,
    - soit sur la relation _ < _ (strictement inférieur)
    - soit sur la relation _ ⇂ _ (divisibilité stricte) *)

(* Le principe d'induction (forte) aussi appelé
   induction bien-fondée ou transfinie, sur les
   entiers naturels. *)
Theorem lt_induction (P : nat → Prop) :
    (∀d, (∀e, e<d → P e) → P d)
   → ∀d,                   P d.
Proof. apply (well_founded_induction lt_wf). Qed.

Section sdiv_wf.

  (* On montre d'abord que tous les entiers positifs
     sont ⇂-accessibles, par induction forte. *)
  Local Lemma Acc_sdiv_S d : Acc sdiv (S d).
  Proof.
    induction d as [ d IH ] using lt_induction.
    constructor; intros [ | e ].
    + (* 0 ne divise pas strictement S d car S d ⇂ 0 *)
      intros [ _ [] ]; auto with div_db.
    + (* S e divise strictement S d alors e < d *)
      intros ?%sdiv_lt; apply IH; lia.
  Qed.

  Hint Resolve Acc_sdiv_S : core.

  (* Puis que 0 est ⇂-accessible. *)
  Local Lemma Acc_sdiv_0 : Acc sdiv 0.
  Proof. constructor 1; intros [] []; auto || easy. Qed.

  Hint Resolve Acc_sdiv_0 : core.

  Lemma sdiv_wf : well_founded sdiv.
  Proof. intros []; auto. Qed.

End sdiv_wf.

(* Et on a déduit un principle d'induction 
   transfinie basé sur la relation bien-fondée
   de divisibilité stricte ⇂. *)
Theorem sdiv_induction (P : nat → Prop) :
    (∀d, (∀e, e⇂d → P e) → P d)
   → ∀d,                   P d.
Proof. apply (well_founded_induction sdiv_wf). Qed.

Check lt_induction.
Check sdiv_induction.
