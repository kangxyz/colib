/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.ReducedExact

/-!
# Actual weight-one point and graph norm dictionaries

The existing whole-support determinant norm is specialized to the original
field. Native prime generators retain their signed integer coefficients.
The first torus-power isomorphism identifies the actual Laurent-evaluation
unit graph; it is not an arbitrary group equivalence or a chosen norm section.

Adapted from Motivic/Cohomology/WeightOne/PointNorm.lean at revision
 a6805c4a87cdfd7717dd7a94039246a167f15380. The native finite-correspondence
subgroup replaces the original free group on integral supports.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.Chow

universe u

namespace AlgebraicGeometry.MotivicCohomology.WeightOne
open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers NativeTorusPolynomial

variable (k : Type u) [Field k]

/-- The original field object, not a separately chosen affine presentation. -/
abbrev point : Cor k := Cor.mk (base (Spec (.of k)))

/-- The actual target of the canonical weight-one reduced quotient. -/
abbrev pointTarget : Cor k := Cor.mk (torusPower (Spec (.of k)) 1)

/-- The literal determinant norm on signed native point correspondences. -/
def pointCycleNorm : (point k ⟶ pointTarget k) →+ Additive kˣ :=
  powerOneNorm (𝟙 (Spec (.of k)))

/-- A unit defines its Laurent-evaluation morphism to the actual first torus power. -/
def rationalPoint (a : kˣ) : base (Spec (.of k)) ⟶ torusPower (Spec (.of k)) 1 :=
  smoothUnitPoint (𝟙 (Spec (.of k))) a ≫ (torusPowerOneIso (Spec (.of k))).inv

/-- The first-power comparison recovers the genuine native unit graph. -/
theorem rationalPoint_graph_powerOne (a : kˣ) :
    powerOneCycleEquiv (𝟙 (Spec (.of k))) ((Cor.graphFunctor k).map (rationalPoint k a)) =
      unitGraphCycle (𝟙 (Spec (.of k))) a (Cor.finite_genericPoints k (point k)) := by
  change ((Cor.graphFunctor k).map
      (smoothUnitPoint (𝟙 (Spec (.of k))) a ≫ (torusPowerOneIso (Spec (.of k))).inv)) ≫
    (Cor.graphFunctor k).map (torusPowerOneIso (Spec (.of k))).hom = _
  erw [CategoryTheory.Functor.map_comp, Category.assoc,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id, graph_smoothUnitPoint]

/-- A literal unit graph has that same unit as determinant norm, without inversion. -/
@[simp] theorem pointCycleNorm_graph (a : kˣ) :
    pointCycleNorm k ((Cor.graphFunctor k).map (rationalPoint k a)) = Additive.ofMul a := by
  change cycleNorm (𝟙 (Spec (.of k)))
    (powerOneCycleEquiv (𝟙 (Spec (.of k))) ((Cor.graphFunctor k).map (rationalPoint k a))) = _
  erw [rationalPoint_graph_powerOne, cycleNorm_unitGraph]

/-- A signed native prime in the original first-power target. -/
def pointGenerator (Z : PrimePoint (𝟙 (Spec (.of k)))) (m : ℤ) :
    point k ⟶ pointTarget k :=
  (powerOneCycleEquiv (𝟙 (Spec (.of k)))).symm
    (singleFiniteCorrespondence (𝟙 (Spec (.of k)))
      (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k)) Z.val Z.property m)

/-- The actual signed generator uses the determinant of its whole support algebra. -/
@[simp] theorem pointCycleNorm_generator (Z : PrimePoint (𝟙 (Spec (.of k)))) (m : ℤ) :
    pointCycleNorm k (pointGenerator k Z m) = m • Additive.ofMul Z.coordinateNorm := by
  change cycleNorm (𝟙 (Spec (.of k)))
    (powerOneCycleEquiv (𝟙 (Spec (.of k)))
      ((powerOneCycleEquiv (𝟙 (Spec (.of k)))).symm _)) = _
  rw [AddEquiv.apply_symm_apply, cycleNorm_single]

/-- Multiplicative notation retains the original signed integer exponent. -/
theorem pointCycleNorm_generator_toMul (Z : PrimePoint (𝟙 (Spec (.of k)))) (m : ℤ) :
    (pointCycleNorm k (pointGenerator k Z m)).toMul = Z.coordinateNorm ^ m := by
  rw [pointCycleNorm_generator]
  rfl

/-- The chosen canonical identity axis is annihilated before homology is formed. -/
@[simp] theorem pointCycleNorm_identityGraph :
    pointCycleNorm k (torusIdentityGraph k (base (Spec (.of k)))) = 0 :=
  powerOneNorm_identityGraph (𝟙 (Spec (.of k)))

/-- The actual reduced quotient has this same point norm on every represented section. -/
theorem reducedPointNorm_toReduced (z : point k ⟶ pointTarget k) :
    reducedNormApp (𝟙 (Spec (.of k)))
      ((toReducedTorus k 1).hom.app (op (point k)) (ULift.up z)) =
        ULift.up (pointCycleNorm k z) :=
  reducedNormApp_toReduced (𝟙 (Spec (.of k))) z

/-- The unit formula already holds on the genuine reduced-torus section. -/
theorem reducedPointNorm_graph (a : kˣ) :
    reducedNormApp (𝟙 (Spec (.of k)))
      ((toReducedTorus k 1).hom.app (op (point k))
        (ULift.up ((Cor.graphFunctor k).map (rationalPoint k a)))) =
      ULift.up (Additive.ofMul a) := by
  erw [reducedPointNorm_toReduced, pointCycleNorm_graph]

/-- Signed multiplicities survive the canonical quotient with their exact norm powers. -/
theorem reducedPointNorm_generator (Z : PrimePoint (𝟙 (Spec (.of k)))) (m : ℤ) :
    reducedNormApp (𝟙 (Spec (.of k)))
      ((toReducedTorus k 1).hom.app (op (point k)) (ULift.up (pointGenerator k Z m))) =
      ULift.up (m • Additive.ofMul Z.coordinateNorm) := by
  rw [reducedPointNorm_toReduced, pointCycleNorm_generator]

end AlgebraicGeometry.MotivicCohomology.WeightOne
