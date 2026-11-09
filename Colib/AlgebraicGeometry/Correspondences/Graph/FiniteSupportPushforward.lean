/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.Postcomposition

/-!
# Graph postcomposition of a finite support map

A finite map from an actual support scheme gives native point cycles weighted by
its residue degrees. Postcomposition with the full graph agrees with pushforward
along the actual postcomposed support map, even when the ambient target map is
not finite. The support scheme may be nonreduced and its generic coefficients
may be arbitrary integers. Every generic component is included, so collisions
and cancellation are preserved.

The component-restriction map, its generic point, and its degree are the native
Stacks `integralComponentMap` APIs. There is no second integral-cycle model or
assumed graph/factorization comparison.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Correspondences/Nisnevich/GeneratorLift.lean`,
`supportLiftImageGenerator_graph`. This native version works directly with the
image point and the existing component-restriction map instead of packaging a
custom integral-image generator.
Native leaf acceptance is recorded separately; no independent review is claimed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin
open scoped BigOperators

attribute [local instance] Stacks.Chow.isIntegral_integralComponentAt
attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

/-- A finite map carries an integral support finite over a source component to
an admissible native image point. This does not assume that its coefficient is nonzero. -/
theorem isFiniteCorrespondencePoint_finiteMap
    {S X Y A : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsSeparated g] [LocallyOfFiniteType g]
    (m : A ⟶ pullback f g) [IsFinite m] (a : A)
    (hfin : IsFinite (((integralComponentAt a).subschemeι ≫ m) ≫ pullback.fst f g))
    (hcomp : Set.range (((integralComponentAt a).subschemeι ≫ m) ≫
      pullback.fst f g) ∈ irreducibleComponents X) :
    IsFiniteCorrespondencePoint f g (m a) := by
  refine ⟨finiteCyclePushforward_isFinite_integralComponentAt m
    (pullback.fst f g) a hfin, ?_⟩
  have hcomp' : (m ≫ pullback.fst f g).base ''
      ((integralComponentAt a).support : Set A) ∈ irreducibleComponents X := by
    simpa only [Category.assoc, finiteCyclePushforward_range_integralComponentAt] using hcomp
  simpa only [finiteCyclePushforward_range_integralComponentAt] using
    finiteCyclePushforward_image_mem_irreducibleComponents m (pullback.fst f g) a hcomp'

section Smooth

variable {k : Type u} [Field k] {X Y Z A : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [Smooth h] [IsSeparated g] [IsSeparated h]
  (q : Y ⟶ Z) (hq : q ≫ h = g)
  (hY : (genericPoints Y).Finite)
  (m : A ⟶ pullback f g) [IsFinite m]
  (j : A ⟶ pullback f h) [IsFinite j]
  (hmj : m ≫ pullback.map f g f h (𝟙 X) q (𝟙 _) (by simp)
    (by simpa using hq.symm) = j)

omit [IsFinite m] [IsSeparated g] in
include hmj in
/-- The native finite image prime followed by the actual graph has exactly the
original postcomposed support degree, with an arbitrary signed coefficient. -/
theorem incidenceTorPairing_finiteImage_single_graph_right_val
    (a : A) (ha : IsFiniteCorrespondencePoint f g (m a)) (n : ℤ) :
    (incidenceTorPairing f g h
      (singleFiniteCorrespondence f g (m a) ha (n * (m.residueDegree a : ℤ)))
      (graphCorrespondenceOfComponents g h q hq hY)).val =
      finiteCyclePushforward j (single a n) := by
  classical
  let e := correspondenceGraphPostcompositionMap f g h q hq (m a)
  let r := integralComponentMap m a
  have hmap : r ≫ e = (integralComponentAt a).subschemeι ≫ j := by
    change integralComponentMap m a ≫ (integralComponentAt (m a)).subschemeι ≫
      pullback.map f g f h (𝟙 X) q (𝟙 _) (by simp)
        (by simpa using hq.symm) = _
    rw [← Category.assoc, integralComponentMap_subschemeι, Category.assoc, hmj]
  have hageneric : (integralComponentAt a).subschemeι
      (genericPoint (integralComponentAt a).subscheme) = a :=
    genericPointOf_integralComponentAt a
  have hdegree : e.residueDegree (genericPoint (integralComponentAt (m a)).subscheme) *
      m.residueDegree a = j.residueDegree a := by
    have he := congrArg
      (fun t : (integralComponentAt a).subscheme ⟶ pullback f h =>
        t.residueDegree (genericPoint (integralComponentAt a).subscheme)) hmap
    simpa only [r, residueDegree_comp, integralComponentMap_base_genericPoint,
      residueDegree_integralComponentMap, residueDegree_eq_one_of_isPreimmersion,
      hageneric, mul_one] using he
  have hpoint : e (genericPoint (integralComponentAt (m a)).subscheme) = j a := by
    rw [show e = correspondenceGraphPostcompositionMap f g h q hq (m a) from rfl,
      correspondenceGraphPostcompositionMap_genericPoint]
    exact congrArg (fun t : A ⟶ pullback f h => t a) hmj
  rw [singleFiniteCorrespondence_eq_zsmul, incidenceTorPairing_zsmul_left]
  change (finiteCorrespondences f h).subtype
    ((n * (m.residueDegree a : ℤ)) •
      incidenceTorPairing f g h (singleFiniteCorrespondence f g (m a) ha 1)
        (graphCorrespondenceOfComponents g h q hq hY)) = _
  rw [map_zsmul]
  change (n * (m.residueDegree a : ℤ)) •
    (incidenceTorPairing f g h (singleFiniteCorrespondence f g (m a) ha 1)
      (graphCorrespondenceOfComponents g h q hq hY)).val = _
  rw [incidenceTorPairing_single_graph_right_val,
    finiteCyclePushforward_single, one_mul, finiteCyclePushforward_single]
  change (n * (m.residueDegree a : ℤ)) •
      single (e (genericPoint (integralComponentAt (m a)).subscheme))
        (e.residueDegree (genericPoint (integralComponentAt (m a)).subscheme) : ℤ) =
    single (j a) (n * (j.residueDegree a : ℤ))
  rw [hpoint]
  have hdegree' : (m.residueDegree a : ℤ) *
      (e.residueDegree (genericPoint (integralComponentAt (m a)).subscheme) : ℤ) =
        (j.residueDegree a : ℤ) := by
    rw [mul_comm, ← Nat.cast_mul, hdegree]
  apply Function.locallyFinsuppWithin.ext
  intro y
  by_cases hy : y = j a
  · simp only [coe_zsmul, Pi.smul_apply, single_apply, hy, ite_true, smul_eq_mul]
    rw [mul_assoc, hdegree']
  · simp [single_apply, hy]

include hmj in
omit [IsSeparated g] in
/-- A complete generic cycle on an actual support scheme lifts as a genuine
finite correspondence. Its native value is the finite pushforward along `m`,
and composition with the full graph is the finite pushforward along `j`.
The only map equation is the literal geometric postcomposition equation. -/
theorem exists_graph_factorization_of_generic_support_map
    (hA : (genericPoints A).Finite) (c : genericPoints A → ℤ)
    (ha : ∀ a : genericPoints A, IsFiniteCorrespondencePoint f g (m a.val)) :
    ∃ β : finiteCorrespondences f g,
      β.val = finiteCyclePushforward m (AlgebraicCycle.ofGenericCoefficients hA c) ∧
      (incidenceTorPairing f g h β
        (graphCorrespondenceOfComponents g h q hq hY)).val =
        finiteCyclePushforward j (AlgebraicCycle.ofGenericCoefficients hA c) := by
  classical
  let := hA.fintype
  let β : finiteCorrespondences f g := ∑ a : genericPoints A,
    singleFiniteCorrespondence f g (m a.val) (ha a)
      (c a * (m.residueDegree a.val : ℤ))
  refine ⟨β, ?_, ?_⟩
  · change (finiteCorrespondences f g).subtype
      (∑ a : genericPoints A, singleFiniteCorrespondence f g (m a.val) (ha a)
        (c a * (m.residueDegree a.val : ℤ))) = _
    rw [map_sum, finiteCyclePushforward_ofGenericCoefficients]
    rfl
  · change (finiteCorrespondences f h).subtype
      ((incidenceTorPairing f g h).flip (graphCorrespondenceOfComponents g h q hq hY)
        (∑ a : genericPoints A, singleFiniteCorrespondence f g (m a.val) (ha a)
          (c a * (m.residueDegree a.val : ℤ)))) = _
    rw [map_sum, map_sum, AlgebraicCycle.ofGenericCoefficients_eq_sum, map_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact incidenceTorPairing_finiteImage_single_graph_right_val
      f g h q hq hY m j hmj a.val (ha a) (c a)

end Smooth

end Stacks.Chow
