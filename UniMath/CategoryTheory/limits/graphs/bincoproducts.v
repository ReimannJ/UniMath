(** ******************************************

Binary coproducts defined as a colimit

Written by: Benedikt Ahrens, March 2015

*********************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.graphs.eqdiag.
Require Import UniMath.CategoryTheory.limits.bincoproducts.

Local Open Scope cat.

(** * Definition of binary coproduct of objects in a precategory *)

Definition two_graph : graph.
Proof.
  exists bool.
  exact (λ _ _, empty).
Defined.

Definition bincoproduct_diagram {C : category} (a b : C) : diagram two_graph C.
Proof.
  exists (λ x : bool, if x then a else b).
  intros u v F.
  induction F.
Defined.

Definition CopCocone {C : category} {a b : C} {c : C} (ac : a --> c) (bc : b --> c) :
   cocone (bincoproduct_diagram a b) c.
Proof.
  use tpair.
+ intro v.
  induction v; simpl.
  - exact ac.
  - exact bc.
+ intros u v e; induction e.
Defined.

Section bincoproduct_def.

Variable C : category.

Definition isBinCoproductCocone (a b co : C) (ia : a --> co) (ib : b --> co) :=
  isColimCocone (bincoproduct_diagram a b) co (CopCocone ia ib).

Definition make_isBinCoproductCocone (hsC : has_homsets C)(a b co : C) (ia : a --> co) (ib : b --> co) :
   (∏ (c : C) (f : a --> c) (g : b --> c),
    ∃! k : C ⟦co, c⟧,
      ia · k = f ×
      ib · k = g)
   →
   isBinCoproductCocone a b co ia ib.
Proof.
  intros H c cc.
  set (H':= H c (coconeIn cc true) (coconeIn cc false)).
  use tpair.
  - exists (pr1 (pr1 H')).
    set (T := pr2 (pr1 H')). simpl in T.
    abstract (intro u; induction u;
              [ apply (pr1 T) | apply (pr2 T)]).
  - simpl. intros. abstract (intros;
              apply subtypePath;
              [ intro; apply impred; intro; apply hsC
              | apply path_to_ctr; split; [ apply (pr2 t true) | apply (pr2 t false)] ]).
Defined.

Definition BinCoproductCocone (a b : C) :=
  ColimCocone (bincoproduct_diagram a b).

Definition make_BinCoproductCocone (a b : C) :
  ∏ (c : C) (f : a --> c) (g : b --> c),
   isBinCoproductCocone _ _ _ f g →  BinCoproductCocone a b.
Proof.
  intros.
  use tpair.
  - exists c.
    apply (CopCocone f g).
  - apply X.
Defined.

Definition BinCoproducts := ∏ (a b : C), BinCoproductCocone a b.
Definition hasBinCoproducts := ∏ (a b : C), ∥ BinCoproductCocone a b ∥.

Definition BinCoproductObject {a b : C} (CC : BinCoproductCocone a b) : C := colim CC.
Definition BinCoproductIn1 {a b : C} (CC : BinCoproductCocone a b): a --> BinCoproductObject CC
  := colimIn CC true.

Definition BinCoproductIn2 {a b : C} (CC : BinCoproductCocone a b) : b --> BinCoproductObject CC
  := colimIn CC false.

Definition BinCoproductArrow {a b : C} (CC : BinCoproductCocone a b) {c : C} (f : a --> c) (g : b --> c) :
      BinCoproductObject CC --> c.
Proof.
  apply (colimArrow CC).
  use make_cocone.
  + intro v. induction v.
    - apply f.
    - apply g.
  + simpl. intros ? ? e; induction e.
Defined.

Lemma BinCoproductIn1Commutes (a b : C) (CC : BinCoproductCocone a b):
     ∏ (c : C) (f : a --> c) g, BinCoproductIn1 CC · BinCoproductArrow CC f g  = f.
Proof.
  intros c f g.
  unfold BinCoproductIn1.
  set (H:=colimArrowCommutes CC  _ (CopCocone f g) true).
  apply H.
Qed.

Lemma BinCoproductIn2Commutes (a b : C) (CC : BinCoproductCocone a b):
     ∏ (c : C) (f : a --> c) g, BinCoproductIn2 CC · BinCoproductArrow CC f g = g.
Proof.
  intros c f g.
  unfold BinCoproductIn1.
  set (H:=colimArrowCommutes CC  _ (CopCocone f g) false).
  apply H.
Qed.

Lemma BinCoproductArrowUnique (a b : C) (CC : BinCoproductCocone a b) (x : C)
    (f : a --> x) (g : b --> x) (k : BinCoproductObject CC --> x) :
    BinCoproductIn1 CC · k = f → BinCoproductIn2 CC · k = g →
      k = BinCoproductArrow CC f g.
Proof.
  intros H1 H2.
  use colimArrowUnique.
  simpl. intro u; induction u; simpl.
  - apply H1.
  - apply H2.
Qed.


Lemma BinCoproductArrowEta (a b : C) (CC : BinCoproductCocone a b) (x : C)
    (f : BinCoproductObject CC --> x) :
    f = BinCoproductArrow CC (BinCoproductIn1 CC · f) (BinCoproductIn2 CC · f).
Proof.
  apply BinCoproductArrowUnique;
  apply idpath.
Qed.


Definition BinCoproductOfArrows {a b : C} (CCab : BinCoproductCocone a b) {c d : C}
    (CCcd : BinCoproductCocone c d) (f : a --> c) (g : b --> d) :
          BinCoproductObject CCab --> BinCoproductObject CCcd :=
    BinCoproductArrow CCab (f · BinCoproductIn1 CCcd) (g · BinCoproductIn2 CCcd).

Lemma BinCoproductOfArrowsIn1 {a b : C} (CCab : BinCoproductCocone a b) {c d : C}
    (CCcd : BinCoproductCocone c d) (f : a --> c) (g : b --> d) :
    BinCoproductIn1 CCab · BinCoproductOfArrows CCab CCcd f g = f · BinCoproductIn1 CCcd.
Proof.
  unfold BinCoproductOfArrows.
  apply BinCoproductIn1Commutes.
Qed.

Lemma BinCoproductOfArrowsIn2 {a b : C} (CCab : BinCoproductCocone a b) {c d : C}
    (CCcd : BinCoproductCocone c d) (f : a --> c) (g : b --> d) :
    BinCoproductIn2 CCab · BinCoproductOfArrows CCab CCcd f g = g · BinCoproductIn2 CCcd.
Proof.
  unfold BinCoproductOfArrows.
  apply BinCoproductIn2Commutes.
Qed.


Lemma precompWithBinCoproductArrow {a b : C} (CCab : BinCoproductCocone a b) {c d : C}
    (CCcd : BinCoproductCocone c d) (f : a --> c) (g : b --> d)
    {x : C} (k : c --> x) (h : d --> x) :
        BinCoproductOfArrows CCab CCcd f g · BinCoproductArrow CCcd k h =
         BinCoproductArrow CCab (f · k) (g · h).
Proof.
  apply BinCoproductArrowUnique.
  - rewrite assoc. rewrite BinCoproductOfArrowsIn1.
    rewrite <- assoc, BinCoproductIn1Commutes.
    apply idpath.
  - rewrite assoc, BinCoproductOfArrowsIn2.
    rewrite <- assoc, BinCoproductIn2Commutes.
    apply idpath.
Qed.


Lemma postcompWithBinCoproductArrow {a b : C} (CCab : BinCoproductCocone a b) {c : C}
    (f : a --> c) (g : b --> c) {x : C} (k : c --> x)  :
       BinCoproductArrow CCab f g · k = BinCoproductArrow CCab (f · k) (g · k).
Proof.
  apply BinCoproductArrowUnique.
  -  rewrite assoc, BinCoproductIn1Commutes;
     apply idpath.
  -  rewrite assoc, BinCoproductIn2Commutes;
     apply idpath.
Qed.

End bincoproduct_def.

Arguments BinCoproductCocone [_] _ _.
Arguments BinCoproductObject [_ _ _] _ .
Arguments BinCoproductArrow [_ _ _] _ [_] _ _.
Arguments BinCoproductIn1 [_ _ _] _.
Arguments BinCoproductIn2 [_ _ _] _.


(** * Proof that coproducts are unique when the precategory [C] is a univalent_category *)

Section coproduct_unique.

Variable C : category.
Hypothesis H : is_univalent C.

Variables a b : C.

Definition from_BinCoproduct_to_BinCoproduct (CC CC' : BinCoproductCocone a b)
  : BinCoproductObject CC --> BinCoproductObject CC'.
Proof.
  apply (BinCoproductArrow CC  (BinCoproductIn1 _ ) (BinCoproductIn2 _ )).
Defined.


Lemma BinCoproduct_endo_is_identity (CC : BinCoproductCocone a b)
  (k : BinCoproductObject CC --> BinCoproductObject CC)
  (H1 : BinCoproductIn1 CC · k = BinCoproductIn1 CC)
  (H2 : BinCoproductIn2 CC · k = BinCoproductIn2 CC)
  : identity _ = k.
Proof.
(*  apply pathsinv0. *)
  use colim_endo_is_identity.
  intro u; induction u; simpl; assumption.
Defined.


Lemma is_z_iso_from_BinCoproduct_to_BinCoproduct (CC CC' : BinCoproductCocone a b)
  : is_z_isomorphism (from_BinCoproduct_to_BinCoproduct CC CC').
Proof.
  exists (from_BinCoproduct_to_BinCoproduct CC' CC).
  split; simpl.
  - apply pathsinv0.
    apply BinCoproduct_endo_is_identity.
    + rewrite assoc. unfold from_BinCoproduct_to_BinCoproduct.
      rewrite BinCoproductIn1Commutes.
      rewrite BinCoproductIn1Commutes.
      apply idpath.
    + rewrite assoc. unfold from_BinCoproduct_to_BinCoproduct.
      rewrite BinCoproductIn2Commutes.
      rewrite BinCoproductIn2Commutes.
      apply idpath.
  - apply pathsinv0.
    apply BinCoproduct_endo_is_identity.
    + rewrite assoc; unfold from_BinCoproduct_to_BinCoproduct.
      repeat rewrite BinCoproductIn1Commutes; apply idpath.
    + rewrite assoc; unfold from_BinCoproduct_to_BinCoproduct.
      repeat rewrite BinCoproductIn2Commutes; apply idpath.
Defined.

Definition z_iso_from_BinCoproduct_to_BinCoproduct (CC CC' : BinCoproductCocone a b)
  : z_iso (BinCoproductObject CC) (BinCoproductObject CC')
  := make_z_iso' _ (is_z_iso_from_BinCoproduct_to_BinCoproduct CC CC').

(* should be an instance of a lemma about colimits *)
(*
Lemma isaprop_BinCoproductCocone : isaprop (BinCoproductCocone a b).
Proof.
  apply invproofirrelevance.
  intros CC CC'.
  apply subtypePath.
  + intros.
    unfold isColimCocone.
    do 2 (apply impred; intro); apply isapropiscontr.
  + apply (total2_paths_f (isotoid _ H (iso_from_BinCoproduct_to_BinCoproduct CC CC'))).
    rewrite transportf_dirprod.
    rewrite transportf_isotoid'. simpl.
    rewrite transportf_isotoid'.
    destruct CC as [CC bla].
    destruct CC' as [CC' bla']; simpl in *.
    destruct CC as [CC [CC1 CC2]].
    destruct CC' as [CC' [CC1' CC2']]; simpl in *.
    unfold from_BinCoproduct_to_BinCoproduct.
    rewrite BinCoproductIn1Commutes.
    rewrite BinCoproductIn2Commutes.
    apply idpath.
Qed.
*)

End coproduct_unique.

Definition limits_isBinCoproductCocone_from_isBinCoproduct (C : category) {a b c}
           (u : C ⟦ a, c⟧)(v : C ⟦ b, c⟧) :
  limits.bincoproducts.isBinCoproduct C a b c u v -> isBinCoproductCocone _ _ _ _ u v :=
  make_isBinCoproductCocone _ C _ _ _ _ _.

Lemma limits_isBinCoproduct_from_isBinCoproductCocone (C : category) {a b c}
      (u : C ⟦ a, c⟧)(v : C ⟦ b, c⟧) :
  isBinCoproductCocone _ _ _ _ u v -> limits.bincoproducts.isBinCoproduct C a b c u v.
Proof.
  intro h.
  set (CC := make_BinCoproductCocone _ _ _ _ _ _ h); simpl.
  intros x f g.
  (* set (CCfg := (bincoproducts.BinCoproductArrow C CC f g)). *)
  use unique_exists; simpl.
  - apply (bincoproducts.BinCoproductArrow CC f g).
  - abstract (split;
              [ apply (bincoproducts.BinCoproductIn1Commutes  _ _ _ CC)
              | apply (bincoproducts.BinCoproductIn2Commutes  _ _ _ CC)]).
  - abstract (intros h'; apply isapropdirprod; apply C).
  - intros h' [H1 H2].
    eapply (bincoproducts.BinCoproductArrowUnique _ _ _ CC).
    + exact H1.
    + exact H2.
Defined.

Lemma BinCoproducts_from_Colims (C : category) :
  Colims_of_shape two_graph C -> BinCoproducts C.
Proof.
now intros H a b; apply H.
Defined.

(** Post-composing a bincoproduct diagram with a functor yields a
     bincoproduct diagram. *)
Lemma mapdiagram_bincoproduct_eq_diag {C : category}{D : category}
      (F : functor C D)(a b : C)  :
  eq_diag (C := D)
          (mapdiagram F (bincoproducts.bincoproduct_diagram a b))
          (bincoproducts.bincoproduct_diagram (F a) (F b)).
Proof.
  use tpair.
  - use bool_rect; apply idpath.
  - intros ??; use empty_rect.
Defined.
