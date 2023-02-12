Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.Combinatorics.Lists.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.limits.graphs.colimits.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.products.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.limits.coproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.categories.HSET.Structures.
Require Import UniMath.CategoryTheory.categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.SubstitutionSystems.Signatures.
Require Import UniMath.SubstitutionSystems.SumOfSignatures.
Require Import UniMath.SubstitutionSystems.BinProductOfSignatures.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.

Require Import UniMath.CategoryTheory.Chains.OmegaContFunctors.

Require Import UniMath.SubstitutionSystems.ContinuitySignature.GeneralLemmas.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.CommutingOfOmegaLimitsAndCoproducts.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.ContinuityOfMultiSortedSigToFunctor.

Local Open Scope cat.

Section OmegaLimitsCommutingWithCoproductsHSET.

  Definition HSET_ω_limits : ∏ coch : cochain HSET, LimCone coch.
  Proof.
    intro coch.
    apply LimConeHSET.
  Defined.

  Lemma TODO_JOKER (A : UU) : A. Proof. Admitted.

  Lemma test {I : HSET} (ind : pr1 I → cochain SET)
        (f : pr111 (limit_of_coproduct SET HSET_ω_limits (CoproductsHSET (pr1 I) (pr2 I)) ind))
    : ∏ n : nat, pr1 (pr1 f n) = pr1 (pr1 f 0).
  Proof.
    induction f as [f p].
    assert (q0 : ∏ n : nat, S n = n + 1).
    {
      intro n ; induction n.
      - apply idpath.
      - apply TODO_JOKER.
    }

    assert (q : ∏ n : nat, pr1 (f (n+1)) = pr1 (f n)).
    { exact (λ n, base_paths _ _ (p (n+1) n (q0 n))). }

    assert (q' : ∏ n : nat, pr1 (f (S n)) = pr1 (f n)).
    {
      intro n.
      refine (_ @ q n).
      apply (maponpaths (λ z, pr1 (f z))).
      exact (q0 n).
    }

    intro n.
    induction n.
    - apply idpath.
    - exact (q' n @ IHn).
  Defined.

  (* Definition test' {I : HSET} (ind : pr1 I -> cochain SET)
    : pr11 (limit_of_coproduct SET HSET_ω_limits (CoproductsHSET (pr1 I) (pr2 I)) ind)
      = ∑ i : I,  *)

  Definition I_coproduct_distribute_over_omega_limit_HSET_inverse
             {I : HSET} (ind : pr1 I → cochain SET)
    :  SET ⟦ pr11 (limit_of_coproduct SET HSET_ω_limits (CoproductsHSET (pr1 I) (pr2 I)) ind),
             pr11 (coproduct_of_limit SET HSET_ω_limits (CoproductsHSET (pr1 I) (pr2 I)) ind) ⟧.
  Proof.
    intros [f p].
    exists (pr1 (f 0)).
    exists (λ n, transportf (λ u, pr1 (dob (ind u) n)) ((test ind (f,,p) n)) (pr2 (f n))).
    intros n m h.

    etrans.
    2: {
      apply maponpaths.
      exact (fiber_paths (p n m h)).
    }
    rewrite transport_f_f.
    cbn.

    induction h.
    induction m.
    - unfold test.
      simpl.
      cbn.
      rewrite pathscomp0rid.




    apply TODO_JOKER.
  Defined.


  Let can := (λ I ind, coproduct_of_limit_to_limit_of_coproduct SET HSET_ω_limits (CoproductsHSET (pr1 I) (pr2 I)) ind).

  Definition I_coproduct_distribute_over_omega_limits_HSET (I : HSET)
    : ω_limits_distribute_over_I_coproducts HSET I HSET_ω_limits (CoproductsHSET (pr1 I) (pr2 I)).
  Proof.
    intro ind.
    use make_is_z_isomorphism.
    - exact (I_coproduct_distribute_over_omega_limit_HSET_inverse ind).
    - split.
      + apply funextsec ; intros [i [f p]].
        use total2_paths_f.
        { apply idpath. }
        use total2_paths_f.
        2: {
          repeat (apply funextsec ; intro).
          apply (pr2 (dob (ind (pr1 (identity (pr11 (coproduct_of_limit SET HSET_ω_limits (CoproductsHSET (pr1 I) (pr2 I)) ind)) _))) _)).
        }

        rewrite idpath_transportf.
        repeat (apply funextsec ; intro).
        apply (transportf_set ((λ u : pr1 I, pr1 (dob (ind u) x)))).
        apply (pr2 I).
      + apply funextsec ; intros [f p].
        use total2_paths_f.
        * apply funextsec ; intro n.
          use total2_paths_f.
          { exact (test ind (f,,p) n). }
          cbn.
          etrans.
          1: apply (transport_f_f (λ x : pr1 I, pr1 (pr1 (ind x) n))).
          etrans.
          1: apply maponpaths_2, pathsinv0l.
          apply (idpath_transportf (λ x : pr1 I, pr1 (pr1 (ind x) n))).
        * repeat (apply funextsec ; intro).
          apply ( dob (coproduct_n_cochain SET (CoproductsHSET (pr1 I) (pr2 I)) ind) _).
  Defined.

End OmegaLimitsCommutingWithCoproductsHSET.

Lemma is_omega_cont_MultiSortedSigToFunctor_HSET
       (sort : UU) (Hsort : isofhlevel 3 sort)
      (M : MultiSortedSig sort)
  : is_omega_cont (MultiSortedSigToFunctor' sort Hsort HSET TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET M).
Proof.
  use is_omega_cont_MultiSortedSigToFunctor'.
  - intro ; apply LimConeHSET.
  - exact I_coproduct_distribute_over_omega_limits_HSET.
Defined.
