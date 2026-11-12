/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.ClosedEndpointGeometry
public import Colib.AlgebraicGeometry.Correspondences.Graph.FiniteSupportPushforward
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.Basic

/-!
# Whole finite-flat closed-family endpoint cycles

The actual graph precomposition is expanded over the original generic points,
with their original self-length weights. Native integral-component restriction
and its actual endpoint pullback identify each term. At a generic whole-fiber
point the local one-parameter devissage assembles these coefficients. Away from
generic source points the actual correspondence vanishes by admissibility.
This last step is essential: no false ungraded component-fiber identity for
arbitrary mixed-dimensional flat families is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace Stacks.Chow

/-- Admissibility forces the actual support point to lie over a generic source point. -/
theorem IsFiniteCorrespondencePoint.source_mem_genericPoints
    {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {z : pullback (C := Scheme) f g} (hz : IsFiniteCorrespondencePoint f g z) :
    pullback.fst f g z ∈ genericPoints X := by
  let W := (integralComponentAt z).subscheme
  let p : W ⟶ X := (integralComponentAt z).subschemeι ≫ pullback.fst f g
  have : IsIntegral W := isIntegral_integralComponentAt z
  have : IsFinite p := hz.1
  have he : closure ({p (genericPoint W)} : Set X) = Set.range p := by
    simpa only [Set.image_singleton, genericPoint_closure, Set.image_univ] using
      p.isClosedMap.closure_image_eq_of_continuous p.continuous ({genericPoint W} : Set W)
  have hg : p (genericPoint W) ∈ genericPoints X := by
    change closure ({p (genericPoint W)} : Set X) ∈ irreducibleComponents X
    rw [he]
    exact hz.2
  have hη : (integralComponentAt z).subschemeι (genericPoint W) = z :=
    genericPointOf_integralComponentAt z
  have hp : p (genericPoint W) = (pullback.fst f g) z :=
    congrArg (fun y => (pullback.fst f g) y) hη
  exact Eq.mp (congrArg (fun y => y ∈ genericPoints X) hp) hg

/-- A genuine correspondence has no coefficients over non-generic source points. -/
theorem finiteCorrespondence_apply_eq_zero_of_notMem_genericSource
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (α : finiteCorrespondences f g) (x : pullback (C := Scheme) f g)
    (hx : pullback.fst f g x ∉ genericPoints X) : α.val x = 0 := by
  by_contra hn
  exact hx (α.property.2 x hn).source_mem_genericPoints

/-- Every original generic component of the whole finite-flat support is admissible. -/
theorem isFiniteCorrespondencePoint_finiteFlat_generic
    {S X Y D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsSeparated g] [LocallyOfFiniteType g]
    (m : D ⟶ pullback f g) [IsFinite m]
    [IsFinite (m ≫ pullback.fst f g)] [Flat (m ≫ pullback.fst f g)]
    (z : genericPoints D) : IsFiniteCorrespondencePoint f g (m z.val) := by
  apply isFiniteCorrespondencePoint_finiteMap f g m z.val
  · simpa only [Category.assoc] using
      (inferInstance : IsFinite ((integralComponentAt z.val).subschemeι ≫
        (m ≫ pullback.fst f g)))
  · simpa only [Category.assoc] using
      finiteFlat_range_integralComponentAt (m ≫ pullback.fst f g) z.val z.property

/-- The existing full span is the sum with the original generic self-lengths. -/
theorem finiteFlatSpanFundamental_eq_sum_single_of_closed
    {S X Y D : Scheme.{u}} [IsNoetherian D] (f : X ⟶ S) (g : Y ⟶ S)
    [IsSeparated g] [LocallyOfFiniteType g]
    (m : D ⟶ pullback f g) [IsClosedImmersion m]
    [IsFinite (m ≫ pullback.fst f g)] [Flat (m ≫ pullback.fst f g)] :
    letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D).fintype
    finiteFlatSpanFundamental f g m = ∑ z : genericPoints D,
      singleFiniteCorrespondence f g (m z.val)
        (isFiniteCorrespondencePoint_finiteFlat_generic f g m z)
        ((Module.length (D.presheaf.stalk z.val) (D.presheaf.stalk z.val)).toNat : ℤ) := by
  classical
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D).fintype
  apply Subtype.ext
  change finiteCyclePushforward m (AlgebraicCycle.fundamentalCycle D) =
    (finiteCorrespondences f g).subtype _
  rw [map_sum]
  unfold AlgebraicCycle.fundamentalCycle
  rw [finiteCyclePushforward_ofGenericCoefficients]
  simp only [residueDegree_eq_one_of_isPreimmersion, Nat.cast_one, mul_one]
  rfl

end Stacks.Chow

namespace AlgebraicGeometry.Cor

open Stacks.Chow _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.AffineLineFiber

variable {k : Type u} [Field k] {X Y Z : Scheme.SmoothSite (Spec (.of k))}
  {D : Scheme.{u}} [IsNoetherian D]
  (φ : X ⟶ Y) (q : Y.left ⟶ Spec (.of (Polynomial k))) [Flat q] (a : k)
  (H : IsPullback φ.left X.hom q (point a))
  (m : D ⟶ pullback Y.hom Z.hom) [IsClosedImmersion m]
  [IsFinite (m ≫ pullback.fst Y.hom Z.hom)] [Flat (m ≫ pullback.fst Y.hom Z.hom)]

omit [IsFinite (m ≫ pullback.fst Y.hom Z.hom)] [Flat (m ≫ pullback.fst Y.hom Z.hom)] in
/-- An admissible original support point has its full original component endpoint cycle. -/
theorem graph_comp_closedSupport_single_val_of_admissible (z : D)
    (hw : IsFiniteCorrespondencePoint Y.hom Z.hom (m z)) :
    letI := isNoetherian_of_finiteType (integralComponentAt z).subschemeι
    ((graphFunctor k).map φ ≫ singleFiniteCorrespondence Y.hom Z.hom (m z)
      hw 1).val =
      finiteCyclePushforward
        (Scheme.AffineLineFiber.fiberMap (m ≫ pullback.fst Y.hom Z.hom ≫ q) a
          (integralComponentAt z).subschemeι ≫
          closedSupportEndpointMap X.hom Y.hom Z.hom φ.left
            (MorphismProperty.Over.w φ) q a H m)
        (AlgebraicCycle.fundamentalCycle
          (fiber ((integralComponentAt z).subschemeι ≫ m ≫
            pullback.fst Y.hom Z.hom ≫ q) a)) := by
  have := isNoetherian_of_finiteType (integralComponentAt z).subschemeι
  have := isNoetherian_correspondenceGraphFiber (X := X.left)
    Y.hom Z.hom (m z) φ.left hw
  have := isFinite_correspondenceGraphFiberMap X.hom Y.hom Z.hom (m z)
    φ.left (MorphismProperty.Over.w φ) hw
  rw [graph_comp_single_val_eq_fiber_of_cartesian_endpoint φ q a H (m z) hw]
  let e := closedSupportComponentEndpointIso X.hom Y.hom Z.hom φ.left q a H m z
  have he := finiteCyclePushforward_fundamentalCycle_iso e
  rw [← he, finiteCyclePushforward_comp_apply]
  have hcongr {A B : Scheme.{u}} {i j : A ⟶ B} [IsFinite i] [IsFinite j]
      (h : i = j) (c : AlgebraicCycle A ℤ) :
      finiteCyclePushforward i c = finiteCyclePushforward j c := by
    cases h
    rfl
  exact hcongr (closedSupportComponentEndpointIso_outer X.hom Y.hom Z.hom φ.left
    (MorphismProperty.Over.w φ) q a H m z) _

/-- Each original generic support term has the actual original component endpoint cycle. -/
theorem graph_comp_closedSupport_single_val (z : genericPoints D) :
    letI := isNoetherian_of_finiteType (integralComponentAt z.val).subschemeι
    ((graphFunctor k).map φ ≫ singleFiniteCorrespondence Y.hom Z.hom (m z.val)
      (isFiniteCorrespondencePoint_finiteFlat_generic Y.hom Z.hom m z) 1).val =
      finiteCyclePushforward
        (Scheme.AffineLineFiber.fiberMap (m ≫ pullback.fst Y.hom Z.hom ≫ q) a
          (integralComponentAt z.val).subschemeι ≫
          closedSupportEndpointMap X.hom Y.hom Z.hom φ.left
            (MorphismProperty.Over.w φ) q a H m)
        (AlgebraicCycle.fundamentalCycle
          (fiber ((integralComponentAt z.val).subschemeι ≫ m ≫
            pullback.fst Y.hom Z.hom ≫ q) a)) :=
  graph_comp_closedSupport_single_val_of_admissible φ q a H m z.val
    (isFiniteCorrespondencePoint_finiteFlat_generic Y.hom Z.hom m z)

/-- Expansion of actual composition retains every original weight and the whole endpoint map. -/
theorem graph_comp_closedFiniteFlatSpan_val_eq_weighted_endpoints :
    letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D).fintype
    letI : ∀ z : genericPoints D, IsNoetherian (integralComponentAt z.val).subscheme :=
      fun z => isNoetherian_of_finiteType (integralComponentAt z.val).subschemeι
    ((graphFunctor k).map φ ≫ finiteFlatSpanFundamental Y.hom Z.hom m).val =
      finiteCyclePushforward
        (closedSupportEndpointMap X.hom Y.hom Z.hom φ.left
          (MorphismProperty.Over.w φ) q a H m)
        (∑ z : genericPoints D,
          ((Module.length (D.presheaf.stalk z.val) (D.presheaf.stalk z.val)).toNat : ℤ) •
            finiteCyclePushforward
              (Scheme.AffineLineFiber.fiberMap (m ≫ pullback.fst Y.hom Z.hom ≫ q) a
                (integralComponentAt z.val).subschemeι)
              (AlgebraicCycle.fundamentalCycle
                (fiber ((integralComponentAt z.val).subschemeι ≫ m ≫
                  pullback.fst Y.hom Z.hom ≫ q) a))) := by
  classical
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D).fintype
  let : ∀ z : genericPoints D, IsNoetherian (integralComponentAt z.val).subscheme :=
    fun z => isNoetherian_of_finiteType (integralComponentAt z.val).subschemeι
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
    (graph_comp_closedSupport_single_val φ q a H m z)

/-- The true whole finite-flat family specializes as its entire actual endpoint,
including all original nilpotents and integral-component multiplicities. -/
theorem graph_comp_closedFiniteFlatSpan_val_eq_whole_endpoint :
    ((graphFunctor k).map φ ≫ finiteFlatSpanFundamental Y.hom Z.hom m).val =
      finiteCyclePushforward
        (closedSupportEndpointMap X.hom Y.hom Z.hom φ.left
          (MorphismProperty.Over.w φ) q a H m)
        (AlgebraicCycle.fundamentalCycle (fiber (m ≫ pullback.fst Y.hom Z.hom ≫ q) a)) := by
  classical
  let := (AlgebraicCycle.fundamentalCycle_genericPoints_finite D).fintype
  let : ∀ z : genericPoints D, IsNoetherian (integralComponentAt z.val).subscheme :=
    fun z => isNoetherian_of_finiteType (integralComponentAt z.val).subschemeι
  have : Flat (m ≫ pullback.fst Y.hom Z.hom ≫ q) := by
    rw [← Category.assoc]
    infer_instance
  let e := closedSupportEndpointMap X.hom Y.hom Z.hom φ.left
    (MorphismProperty.Over.w φ) q a H m
  have : IsFinite (e ≫ pullback.fst X.hom Z.hom) := by
    dsimp [e]
    rw [closedSupportEndpointMap_fst]
    infer_instance
  have : Flat (e ≫ pullback.fst X.hom Z.hom) := by
    dsimp [e]
    rw [closedSupportEndpointMap_fst]
    infer_instance
  let β : Cor.mk X ⟶ Cor.mk Z :=
    (graphFunctor k).map φ ≫ finiteFlatSpanFundamental Y.hom Z.hom m
  have hw := graph_comp_closedFiniteFlatSpan_val_eq_weighted_endpoints φ q a H m
  change β.val = finiteCyclePushforward e _ at hw
  apply Function.locallyFinsuppWithin.ext
  intro x
  change β.val x =
    finiteCyclePushforward e
      (AlgebraicCycle.fundamentalCycle (fiber (m ≫ pullback.fst Y.hom Z.hom ≫ q) a)) x
  by_cases hx : x ∈ Set.range e
  · obtain ⟨y, rfl⟩ := hx
    rw [finiteCyclePushforward_apply_of_isClosedImmersion]
    by_cases hy : y ∈ genericPoints (fiber (m ≫ pullback.fst Y.hom Z.hom ≫ q) a)
    · rw [hw, finiteCyclePushforward_apply_of_isClosedImmersion]
      simpa only [coe_sum, Finset.sum_apply, coe_zsmul, Pi.smul_apply, smul_eq_mul] using
        (fundamentalCycle_apply_eq_sum_componentFibers
          (m ≫ pullback.fst Y.hom Z.hom ≫ q) a ⟨y, hy⟩).symm
    · rw [AlgebraicCycle.fundamentalCycle_apply_of_notMem _ y hy]
      exact finiteCorrespondence_apply_eq_zero_of_notMem_genericSource X.hom Z.hom β (e y)
        (fun hgen => hy (mem_genericPoints_of_isFinite_image
          (e ≫ pullback.fst X.hom Z.hom) y hgen))
  · rw [hw]
    have hz (c : AlgebraicCycle (fiber (m ≫ pullback.fst Y.hom Z.hom ≫ q) a) ℤ) :
        finiteCyclePushforward e c x = 0 := by
      by_contra hn
      obtain ⟨y, _, he⟩ := finiteCyclePushforward_support_subset e c hn
      exact hx ⟨y, he⟩
    exact (hz _).trans (hz _).symm

end AlgebraicGeometry.Cor
