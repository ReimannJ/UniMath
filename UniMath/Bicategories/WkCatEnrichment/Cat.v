(** **********************************************************

Mitchell Riley

June 2016

I am very grateful to Peter LeFanu Lumsdaine, whose unreleased
bicategories code strongly influenced the proofs in this file.

************************************************************)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.categories.StandardCategories. (* unit *)
Require Import UniMath.CategoryTheory.HorizontalComposition.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Local Open Scope cat.
Require Import UniMath.Bicategories.WkCatEnrichment.prebicategory.



(******************************************************************************)
(* Lemmas for use in PreCat and Cat *)

Definition Catlike_associator ( a b c d : category )
  :
   nat_trans
     (functor_composite
        (pair_functor
           (functor_identity (functor_category a b))
           (functorial_composition b c d ))
        (functorial_composition a b d ))
     (functor_composite
        (precategory_binproduct_assoc (functor_category a b )
           (functor_category b c)
           (functor_category c d ))
        (functor_composite
           (pair_functor
              (functorial_composition a b c )
              (functor_identity (functor_category c d)))
           (functorial_composition a c d ))).
Proof.
  use tpair.
  - (* Step 1: Give the components of the natural transformation *)
    (* I.e., for every triple of functors
         F : a -> b
         G : b -> c
         H : c -> d,
       a natural transformation F (G H) -> (F G) H *)

    intros x.
    simpl.

    (* The component at x is just the identity, because composition of
       functions is associative for free. *)
    exists (λ x, identity _).

    (* Which is natural. *)
    intros oba oba' f.
    use (id_right _ @ !(id_left _)).

  - (* Step 2: Show the above is natural, so given
       f : F -> F', g : G -> G', h : H -> H', *)
    intros [F  [G  H]].
    intros [F' [G' H']].
    intros [f  [g  h]].
    (* Verify that
       (f, (g, h)) ∘ (assoc F' G' H') = (assoc F G H) ∘ ((f, g), h))
       as natural transformations. *)

    (* To show two natural transformations are equal, suffices to
       check components *)
    apply (nat_trans_eq_alt).
    intros oba.

    simpl. do 2 (unfold horcomp_data; simpl).

    (* Now assoc is just identity *)
    rewrite id_right.
    rewrite id_left.

    (* And the order we do f, g, h doesn't matter *)
    rewrite (functor_comp H).
    rewrite assoc.
    apply idpath.
Defined.

Definition Catlike_associator_is_iso ( a b c d : category )
  : ∏ f g h, is_iso (Catlike_associator a b c d
                    (make_catbinprod f (make_catbinprod g h))).
Proof.
  intros f g h.
  (* The components are all the identity, so this is easy *)
  apply functor_iso_if_pointwise_iso.
  intros oba.
  apply (identity_is_iso d).
Defined.

Definition Catlike_left_unitor (a b : category)
  :
  nat_trans
     (functor_composite
        (bindelta_pair_functor
           (functor_composite (functor_to_unit (functor_category a b))
              (constant_functor unit_category (functor_category a a) (functor_identity a)))
           (functor_identity (functor_category a b)))
        (functorial_composition a a b))
     (functor_identity (functor_category a b)).
Proof.
  use tpair.
  - (* Step 1: Give components.
       Again identity works, as function composition is unital for free *)
    intros x.
    exists (λ x, identity _).
    intros oba oba' f.
    exact (id_right _ @ !(id_left _)).

  - (* Step 2: Show the above is natural, so given f : F -> F' *)
    intros F F' f.
    (* Verify that
       (f, id) ∘ (left_unitor F') = (left_unitor F) ∘ f
       as natural transformations. *)

    (* Again just check components *)
    apply (nat_trans_eq_alt).
    intros oba.

    simpl. unfold horcomp_data; simpl.
    rewrite id_right.
    rewrite id_left.
    rewrite (functor_id F).
    apply id_left.
Defined.

Definition Catlike_left_unitor_is_iso (a b : category)
  : ∏ f, is_iso (Catlike_left_unitor a b f).
Proof.
  intros f.
  apply functor_iso_if_pointwise_iso.
  intros oba.
  apply (identity_is_iso b).
Defined.

Definition Catlike_right_unitor (a b : category)
  :
  nat_trans
     (functor_composite
        (bindelta_pair_functor (functor_identity (functor_category a b))
           (functor_composite (functor_to_unit (functor_category a b))
              (constant_functor unit_category (functor_category b b) (functor_identity b))))
        (functorial_composition a b b))
     (functor_identity (functor_category a b)).
Proof.
  use tpair. (* Same as above *)
  - intros x.
    exists (λ x, identity _).
    intros oba oba' f.
    exact (id_right _ @ !(id_left _)).

  - intros F F' f.
    apply (nat_trans_eq_alt).
    intros oba.

    simpl. unfold horcomp_data; simpl.
    rewrite (id_right _).
    rewrite (id_left _).
    apply id_right.
Defined.

Definition Catlike_right_unitor_is_iso (a b : category) :
  ∏ f, is_iso (Catlike_right_unitor a b f).
Proof.
  intros f.
  apply functor_iso_if_pointwise_iso.
  intros oba.
  apply (identity_is_iso b).
Defined.

(* What a mess! *)
Definition Catlike_pentagon ( a b c d e : category )
  (hsB : has_homsets b) (hsC : has_homsets c) (hsD : has_homsets d)
  (hsE : has_homsets e) :
  ∏ k h g f,
  (Catlike_associator a b c e )
     (make_catbinprod k
        (make_catbinprod h ((functorial_composition c d e ) (make_dirprod g f)))) ·
   (Catlike_associator a c d e )
     (make_catbinprod ((functorial_composition_legacy a b c) (make_dirprod k h))
        (make_catbinprod g f))
  = (functor_on_morphisms (functorial_composition_legacy a b e)
      (catbinprodmor (identity k)
         ((Catlike_associator b c d e) (make_catbinprod h (make_catbinprod g f)))) ·
    (Catlike_associator a b d e )
      (make_catbinprod k
         (make_catbinprod ((functorial_composition_legacy b c d ) (make_dirprod h g)) f))) ·
   functor_on_morphisms (functorial_composition_legacy a d e )
     (catbinprodmor
        ((Catlike_associator a b c d ) (make_catbinprod k (make_catbinprod h g)))
        (identity f)).
Proof.
  intros k h g f.
  apply (nat_trans_eq hsE).

  intros oba.
  simpl. unfold horcomp_data; simpl.

  (* Everything boils down to the identity *)
  repeat rewrite functor_id.
  repeat rewrite (id_left _).
  apply idpath.
Defined.

Definition Catlike_triangle ( a b c : category )
  :
   ∏ f g, functor_on_morphisms (functorial_composition_legacy a b c)
                               (catbinprodmor (identity f) (Catlike_left_unitor b c g))
   =
      (Catlike_associator a b b c
        (make_catbinprod f (make_catbinprod (functor_identity b : [ _, _] ) g)))
   · functor_on_morphisms (functorial_composition_legacy a b c)
                           (catbinprodmor (Catlike_right_unitor a b f) (identity g)).
Proof.
  intros f g.
  apply (nat_trans_eq c).
  intros oba.
  simpl. unfold horcomp_data; simpl.
  repeat rewrite functor_id.
  repeat rewrite (id_left _).
  apply idpath.
Defined.

(******************************************************************************)
(* The prebicategory of precategories *)

Definition PreCat_1mor_2mor : prebicategory_ob_hom.
Proof.
  exists category.
  intros a b.
  exact (functor_category a b).
Defined.

Definition PreCat_id_comp : prebicategory_id_comp.
Proof.
  exists PreCat_1mor_2mor.
  split.
  - simpl.
    exact functor_identity.
  - simpl.
    intros a b c.
    exact (functorial_composition_legacy a b c).
Defined.


(*
Definition PreCat_data : prebicategory_data.
Proof.
  unfold prebicategory_data.
  exists PreCat_id_comp.
  repeat split.
  - intros.
    simpl in a,b,c,d.
    exact (Catlike_associator a b c d ).
  - intros.
    simpl in a, b.
    exact (Catlike_left_unitor a b (homset_property a)
                                   (homset_property b)).
  - intros.
    simpl in a, b.
    exact (Catlike_right_unitor a b (homset_property b)).
Defined.

Definition PreCat_has_2mor_set : has_2mor_sets PreCat_data.
Proof.
  unfold has_2mor_sets.
  intros a b f g.
  apply isaset_nat_trans.
  exact (homset_property b).
Defined.

Definition PreCat_associator_and_unitors_are_iso : associator_and_unitors_are_iso PreCat_data.
Proof.
  repeat split.
  - intros a b c d.
    apply Catlike_associator_is_iso.
  - intros a b.
    apply Catlike_left_unitor_is_iso.
  - intros a b.
    apply Catlike_right_unitor_is_iso.
Defined.

Definition PreCat_coherence : prebicategory_coherence PreCat_data.
Proof.
  unfold prebicategory_coherence.
  split.
  - intros a b c d e.
    apply Catlike_pentagon.
  - intros a b c.
    apply Catlike_triangle.
Defined.

Definition PreCat : prebicategory.
Proof.
  use tpair.
  exact PreCat_data.
  split.
  exact PreCat_has_2mor_set.
  split.
  exact PreCat_associator_and_unitors_are_iso.
  exact PreCat_coherence.
Defined.

(******************************************************************************)
(* The bicategory of categories *)

Definition Cat_1mor_2mor : prebicategory_ob_hom.
Proof.
  exists univalent_category.
  intros a b.
  exact (functor_precategory a b (univalent_category_has_homsets b)).
Defined.

Definition Cat_id_comp : prebicategory_id_comp.
Proof.
  exists Cat_1mor_2mor.
  split.
  - simpl.
    exact functor_identity.
  - simpl.
    intros a b c.
    exact (functorial_composition_legacy a b c (univalent_category_has_homsets b)
                                        (univalent_category_has_homsets c)).
Defined.

Definition Cat_data : prebicategory_data.
Proof.
  unfold prebicategory_data.
  exists Cat_id_comp.
  repeat split.
  - intros.
    simpl in a,b,c,d.
    exact (Catlike_associator a b c d (univalent_category_has_homsets b)
                                      (univalent_category_has_homsets c)
                                      (univalent_category_has_homsets d)).
  - intros.
    simpl in a, b.
    exact (Catlike_left_unitor a b (univalent_category_has_homsets a)
                                   (univalent_category_has_homsets b)).
  - intros.
    simpl in a, b.
    exact (Catlike_right_unitor a b (univalent_category_has_homsets b)).
Defined.

Definition Cat_has_2mor_set : has_2mor_sets Cat_data.
Proof.
  unfold has_2mor_sets.
  intros a b f g.
  apply isaset_nat_trans.
  exact (univalent_category_has_homsets b).
Defined.

Definition Cat_associator_and_unitors_are_iso : associator_and_unitors_are_iso Cat_data.
Proof.
  repeat split.
  - intros a b c d.
    apply Catlike_associator_is_iso.
  - intros a b.
    apply Catlike_left_unitor_is_iso.
  - intros a b.
    apply Catlike_right_unitor_is_iso.
Defined.

Definition Cat_coherence : prebicategory_coherence Cat_data.
Proof.
  split.
  - intros a b c d e.
    apply Catlike_pentagon.
  - intros a b c.
    apply Catlike_triangle.
Defined.

Definition Cat_prebicategory : prebicategory.
Proof.
  use tpair.
  exact Cat_data.
  unfold is_prebicategory.
  split.
  exact Cat_has_2mor_set.
  split.
  exact Cat_associator_and_unitors_are_iso.
  exact Cat_coherence.
Defined.

Definition Cat_has_homcats : has_homcats Cat_prebicategory.
Proof.
  unfold has_homcats.
  intros a b.
  apply is_univalent_functor_category.
  apply b.
Defined.

(* TODO: "Should be easy" *)

(* Definition Cat_is_lt2saturated (a b : Cat_prebicategory) *)
(*   : isweq (id_to_internal_equivalence a b). *)
(* Proof. *)

(* Definition Cat : bicategory. *)
(* Proof. *)
(*   exists Cat_prebicategory. *)
(*   split. *)
(*   - exact Cat_has_homcats. *)
(*   - exact Cat_is_lt2saturated. *)
(* Defined. *)

 *)
