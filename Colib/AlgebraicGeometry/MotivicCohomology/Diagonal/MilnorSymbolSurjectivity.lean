/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.PointPresentation
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.PolynomialNormComparisonAll

/-!
# Surjectivity of the diagonal Milnor symbol

The finite norm comparison sends the norm of the coordinates of a closed
point to its actual signed cycle class. These classes generate the diagonal
homology over any field.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalMilnorEquivalence

open _root_.AlgebraicGeometry.Scheme
open PresheafWithTransfers DiagonalTopDegree DiagonalCycleSymbols
open DiagonalPointNorm DiagonalPointPresentation DiagonalMilnorSymbol
open DiagonalCorestriction (corestriction)
open DiagonalPolynomialNormComparisonAll (rawSymbol_milnorKNorm)

variable (k : Type u) [Field k] (q : ℕ)

/-- Norm evaluation on a native coefficient-one point recovers its actual cycle class. -/
theorem rawSymbol_generatorValue (Z : Generator k q) :
    rawSymbol k q (generatorValue Z) =
      cycleClass k q (singleFiniteCorrespondence _ _ Z.val Z.property 1) := by
  let N := coordinateRing Z
  let a : Fin q → Nˣ := coordinateUnit Z
  let tr := corestriction (k := k) (E := N) q
  calc
    _ = tr (rawSymbol N q (milnorKTupleSymbol a)) :=
      rawSymbol_milnorKNorm (k := k) (E := N) q (milnorKTupleSymbol a)
    _ = tr (graphSymbol N q a) := congrArg tr (rawSymbol_symbol N q a)
    _ = _ := (cycleClass_generator Z).symm

/-- Norm evaluation followed by the graph map recovers the class of every signed point cycle. -/
theorem rawSymbol_cycleValue (α : point k ⟶ target k q) :
    rawSymbol k q (cycleValue k q α) = cycleClass k q α := by
  have h : (rawSymbol k q).comp (cycleValue k q) = cycleClass k q := by
    apply finiteCorrespondences.addHom_ext_one (𝟙 (Spec (.of k)))
      (SmoothSite.torusPower (Spec (.of k)) q).hom
    intro z hz
    let Z : Generator k q := ⟨z, hz⟩
    exact (congrArg (rawSymbol k q) (cycleValue_cycle Z)).trans
      (rawSymbol_generatorValue k q Z)
  exact DFunLike.congr_fun h α

/-- The actual graph symbol surjects onto the integral raw diagonal group. -/
theorem rawSymbol_surjective : Function.Surjective (rawSymbol k q) := by
  intro x
  obtain ⟨α, rfl⟩ := DiagonalCorestriction.cycleClass_surjective k q x
  exact ⟨cycleValue k q α, rawSymbol_cycleValue k q α⟩

end AlgebraicGeometry.MotivicCohomology.DiagonalMilnorEquivalence
