/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingExteriorMultiplicity
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor

/-!
# Native flat-cycle weights at original exterior generic labels

A generic point of the full last-pair-incidence exterior is also generic in the
full scheme-theoretic inverse image of the reduced closure of its original
label. Native Stacks 02RB therefore identifies its flat-cycle multiplicity
with the existing closed-fibre length. The correct dimension grade is kept
explicit: a different grade contributes zero. This comparison does not assume
that different components of a smooth ambient scheme have the same dimension.

The closed-fibre quotient is not reduced. In particular the comparison keeps
the full inseparable exterior multiplicity over an arbitrary field. The
finiteness certificate used in the correspondence Euler context is supplied
separately by `RemainingExteriorFiberLength`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- A whole exterior generic label remains generic in the full inverse image of its
original point closure. This is a proved property, not a chosen comparison label. -/
theorem exists_correspondenceRightExteriorGeneric_comap
    (η : genericPoints (correspondenceRightIntermediateSupportProduct f g h i z w v)) :
    let π := correspondenceRightExteriorProjection f g h i z w v
    ∃ ξ : genericPoints ((integralComponentAt (π η.1)).comap π).subscheme,
      ((integralComponentAt (π η.1)).comap π).subschemeι ξ.1 = η.1 := by
  dsimp only
  let π := correspondenceRightExteriorProjection f g h i z w v
  obtain ⟨ξ, hξ, _⟩ := exists_comap_genericPoint_over π (π η.1) η.1 rfl
  have hs := specializes_iff_mem_closure.mpr hξ
  have hr := genericPoint_isMax η.1 η.2 hs
  exact ⟨ξ, (hs.antisymm hr).eq⟩

/-- At its actual point dimension, the native cycle weight is the full existing fibre factor. -/
theorem flatPullbackWeight_correspondenceRightExterior_generic
    (C : ChowSituation.{u}) (sE : (correspondenceRightIntermediateSupportProduct f g h i z w v) ⟶
      C.S) [LocallyOfFiniteType sE]
    (η : genericPoints (correspondenceRightIntermediateSupportProduct f g h i z w v)) :
    let π := correspondenceRightExteriorProjection f g h i z w v
    flatPullbackWeight C sE π (relativeDimension C.dimensionFunction sE η.1) η.1 =
      (correspondenceRightExteriorFiberLength f g h i z w v η.1 : ℤ) := by
  dsimp only
  let π := correspondenceRightExteriorProjection f g h i z w v
  exact flatPullbackWeight_eq_length_quotient_extendedMaximalIdeal C sE π _ η.1
    (exists_correspondenceRightExteriorGeneric_comap f g h i z w v η) rfl

/-- The dimension filter in native cycle pullback is retained rather than silently erased. -/
theorem flatPullbackWeight_correspondenceRightExterior_generic_grade
    (C : ChowSituation.{u}) (sE : (correspondenceRightIntermediateSupportProduct f g h i z w v) ⟶
      C.S) [LocallyOfFiniteType sE]
    (η : genericPoints (correspondenceRightIntermediateSupportProduct f g h i z w v)) (j : ℤ) :
    let π := correspondenceRightExteriorProjection f g h i z w v
    flatPullbackWeight C sE π j η.1 =
      if relativeDimension C.dimensionFunction sE η.1 = j then
        (correspondenceRightExteriorFiberLength f g h i z w v η.1 : ℤ) else 0 := by
  dsimp only
  classical
  by_cases hd : relativeDimension C.dimensionFunction sE η.1 = j
  · rw [ite_eq_left hd, ← hd]
    exact flatPullbackWeight_correspondenceRightExterior_generic f g h i z w v C sE η
  · rw [ite_eq_right hd]
    unfold flatPullbackWeight closedSubschemeCycleCoeff
    rw [dite_eq_right]
    rintro ⟨_, _, hj⟩
    exact hd hj

end Stacks.Chow
