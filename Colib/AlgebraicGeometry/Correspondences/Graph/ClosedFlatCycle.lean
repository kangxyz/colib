/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.ClosedFlatGeometry
public import Colib.AlgebraicGeometry.Correspondences.Graph.ClosedEndpointCycle
public import Colib.AlgebraicGeometry.Chow.FlatComponentCoefficient

/-!
# Whole closed finite-flat spans under flat graph precomposition

The original generic weights are retained in the full Cartesian component
pullbacks. Actual flat local length multiplicativity assembles the coefficient
at generic points of the whole pullback. Admissibility handles the remaining
points, including empty and disconnected sources. No integral component is
assumed flat over the original source.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Cor

open Stacks.Chow _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X Y Z : Scheme.SmoothSite (Spec (.of k))}
  {D : Scheme.{u}} [IsNoetherian D]
  (φ : X ⟶ Y) [Flat φ.left]
  (m : D ⟶ pullback Y.hom Z.hom) [IsClosedImmersion m]
  [IsFinite (m ≫ pullback.fst Y.hom Z.hom)] [Flat (m ≫ pullback.fst Y.hom Z.hom)]

omit [IsNoetherian D] in
/-- A prime original term retains its actual entire comap component and outer map. -/
theorem graph_comp_closedSupport_single_val_of_flat (z : genericPoints D) :
    letI := isNoetherian_of_finiteType
      (pullback.fst φ.left (m ≫ pullback.fst Y.hom Z.hom))
    letI := isNoetherian_of_finiteType
      ((integralComponentAt z.val).comap
        (pullback.snd φ.left (m ≫ pullback.fst Y.hom Z.hom))).subschemeι
    ((graphFunctor k).map φ ≫ singleFiniteCorrespondence Y.hom Z.hom (m z.val)
      (isFiniteCorrespondencePoint_finiteFlat_generic Y.hom Z.hom m z) 1).val =
      finiteCyclePushforward
        (((integralComponentAt z.val).comap
          (pullback.snd φ.left (m ≫ pullback.fst Y.hom Z.hom))).subschemeι ≫
            closedSupportGraphFiberMap X.hom Y.hom Z.hom m φ.left
              (MorphismProperty.Over.w φ))
        (AlgebraicCycle.fundamentalCycle
          ((integralComponentAt z.val).comap
            (pullback.snd φ.left (m ≫ pullback.fst Y.hom Z.hom))).subscheme) := by
  have := isNoetherian_of_finiteType
    (pullback.fst φ.left (m ≫ pullback.fst Y.hom Z.hom))
  have := isNoetherian_of_finiteType
    ((integralComponentAt z.val).comap
      (pullback.snd φ.left (m ≫ pullback.fst Y.hom Z.hom))).subschemeι
  let hw := isFiniteCorrespondencePoint_finiteFlat_generic Y.hom Z.hom m z
  have := isNoetherian_correspondenceGraphFiber (X := X.left)
    Y.hom Z.hom (m z.val) φ.left hw
  have := isFinite_correspondenceGraphFiberMap X.hom Y.hom Z.hom (m z.val)
    φ.left (MorphismProperty.Over.w φ) hw
  rw [graph_comp_single_val_eq_fiber_of_flat φ (m z.val) hw]
  let e := closedSupportComponentFlatIso Y.hom Z.hom m φ.left z.val
  rw [← finiteCyclePushforward_fundamentalCycle_iso e, finiteCyclePushforward_comp_apply]
  have hcongr {A B : Scheme.{u}} {i j : A ⟶ B} [IsFinite i] [IsFinite j]
      (h : i = j) (c : AlgebraicCycle A ℤ) :
      finiteCyclePushforward i c = finiteCyclePushforward j c := by
    cases h
    rfl
  exact hcongr (closedSupportComponentFlatIso_outer X.hom Y.hom Z.hom m φ.left
    (MorphismProperty.Over.w φ) z.val) _

/-- Actual composition is the original length-weighted sum of full component pullbacks. -/
theorem graph_comp_closedFiniteFlatSpan_val_eq_weighted_flat_pullbacks :
    letI := isNoetherian_of_finiteType
      (pullback.fst φ.left (m ≫ pullback.fst Y.hom Z.hom))
    letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D).fintype
    letI : ∀ z : genericPoints D, IsNoetherian
        ((integralComponentAt z.val).comap
          (pullback.snd φ.left (m ≫ pullback.fst Y.hom Z.hom))).subscheme :=
      fun z => isNoetherian_of_finiteType
        ((integralComponentAt z.val).comap
          (pullback.snd φ.left (m ≫ pullback.fst Y.hom Z.hom))).subschemeι
    ((graphFunctor k).map φ ≫ finiteFlatSpanFundamental Y.hom Z.hom m).val =
      finiteCyclePushforward
        (closedSupportGraphFiberMap X.hom Y.hom Z.hom m φ.left
          (MorphismProperty.Over.w φ))
        (∑ z : genericPoints D,
          ((Module.length (D.presheaf.stalk z.val) (D.presheaf.stalk z.val)).toNat : ℤ) •
            finiteCyclePushforward
              ((integralComponentAt z.val).comap
                (pullback.snd φ.left (m ≫ pullback.fst Y.hom Z.hom))).subschemeι
              (AlgebraicCycle.fundamentalCycle
                ((integralComponentAt z.val).comap
                  (pullback.snd φ.left (m ≫ pullback.fst Y.hom Z.hom))).subscheme)) := by
  classical
  have := isNoetherian_of_finiteType
    (pullback.fst φ.left (m ≫ pullback.fst Y.hom Z.hom))
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D).fintype
  let : ∀ z : genericPoints D, IsNoetherian
      ((integralComponentAt z.val).comap
        (pullback.snd φ.left (m ≫ pullback.fst Y.hom Z.hom))).subscheme :=
    fun z => isNoetherian_of_finiteType
        ((integralComponentAt z.val).comap
          (pullback.snd φ.left (m ≫ pullback.fst Y.hom Z.hom))).subschemeι
  rw [finiteFlatSpanFundamental_eq_sum_single_of_closed, Preadditive.comp_sum]
  change (finiteCorrespondences X.hom Z.hom).subtype _ = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [singleFiniteCorrespondence_eq_zsmul, Preadditive.comp_zsmul]
  change (finiteCorrespondences X.hom Z.hom).subtype (_ • _) = _
  rw [map_zsmul, map_zsmul, finiteCyclePushforward_comp_apply]
  exact congrArg (fun c => ((Module.length (D.presheaf.stalk z.val)
    (D.presheaf.stalk z.val)).toNat : ℤ) • c)
    (graph_comp_closedSupport_single_val_of_flat φ m z)

/-- A flat graph pulls the entire finite-flat closed family back, with its true weights. -/
theorem graph_comp_closedFiniteFlatSpan_val_eq_whole_flat_pullback :
    letI := isNoetherian_of_finiteType
      (pullback.fst φ.left (m ≫ pullback.fst Y.hom Z.hom))
    ((graphFunctor k).map φ ≫ finiteFlatSpanFundamental Y.hom Z.hom m).val =
      finiteCyclePushforward
        (closedSupportGraphFiberMap X.hom Y.hom Z.hom m φ.left
          (MorphismProperty.Over.w φ))
        (AlgebraicCycle.fundamentalCycle
          (pullback φ.left (m ≫ pullback.fst Y.hom Z.hom))) := by
  classical
  have := isNoetherian_of_finiteType
    (pullback.fst φ.left (m ≫ pullback.fst Y.hom Z.hom))
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D).fintype
  let : ∀ z : genericPoints D, IsNoetherian
      ((integralComponentAt z.val).comap
        (pullback.snd φ.left (m ≫ pullback.fst Y.hom Z.hom))).subscheme :=
    fun z => isNoetherian_of_finiteType
        ((integralComponentAt z.val).comap
          (pullback.snd φ.left (m ≫ pullback.fst Y.hom Z.hom))).subschemeι
  let e := closedSupportGraphFiberMap X.hom Y.hom Z.hom m φ.left
    (MorphismProperty.Over.w φ)
  have : IsFinite (e ≫ pullback.fst X.hom Z.hom) := by
    dsimp [e]
    rw [closedSupportGraphFiberMap_fst]
    infer_instance
  have : Flat (e ≫ pullback.fst X.hom Z.hom) := by
    dsimp [e]
    rw [closedSupportGraphFiberMap_fst]
    infer_instance
  let β : Cor.mk X ⟶ Cor.mk Z :=
    (graphFunctor k).map φ ≫ finiteFlatSpanFundamental Y.hom Z.hom m
  have hw := graph_comp_closedFiniteFlatSpan_val_eq_weighted_flat_pullbacks φ m
  change β.val = finiteCyclePushforward e _ at hw
  apply Function.locallyFinsuppWithin.ext
  intro x
  change β.val x = finiteCyclePushforward e
    (AlgebraicCycle.fundamentalCycle (pullback φ.left (m ≫ pullback.fst Y.hom Z.hom))) x
  by_cases hx : x ∈ Set.range e
  · obtain ⟨y, rfl⟩ := hx
    rw [finiteCyclePushforward_apply_of_isClosedImmersion]
    by_cases hy : y ∈ genericPoints
        ↥(pullback (C := Scheme) φ.left (m ≫ pullback.fst Y.hom Z.hom))
    · rw [hw, finiteCyclePushforward_apply_of_isClosedImmersion]
      simpa only [coe_sum, Finset.sum_apply, coe_zsmul, Pi.smul_apply, smul_eq_mul] using
        (fundamentalCycle_apply_eq_sum_flat_components
          (pullback.snd φ.left (m ≫ pullback.fst Y.hom Z.hom)) ⟨y, hy⟩).symm
    · rw [AlgebraicCycle.fundamentalCycle_apply_of_notMem _ y hy]
      exact finiteCorrespondence_apply_eq_zero_of_notMem_genericSource X.hom Z.hom β (e y)
        (fun hgen => hy (mem_genericPoints_of_isFinite_image
          (e ≫ pullback.fst X.hom Z.hom) y hgen))
  · rw [hw]
    have hz (c : AlgebraicCycle (pullback φ.left (m ≫ pullback.fst Y.hom Z.hom)) ℤ) :
        finiteCyclePushforward e c x = 0 := by
      by_contra hn
      obtain ⟨y, _, he⟩ := finiteCyclePushforward_support_subset e c hn
      exact hx ⟨y, he⟩
    exact (hz _).trans (hz _).symm

end AlgebraicGeometry.Cor
