/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.MarkedGraphFrame

/-!
# Whole-scheme and pointwise base change of the specified marked frame

The coordinate equation is preserved by the actual map on global sections for
any change of source. In particular the source may be an entire unreduced fibre
or `Spec K`; no geometric-point or reduction substitute is made.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable (R B : Type u) [CommRing R] [CommRing B] (z : R[X] →+* B)
  {C Y : Scheme.{u}} (q : C ⟶ Spec (.of R)) [IsSeparated q]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
  (p : Y ⟶ Spec (.of R[X])) (hq : j ≫ q = p ≫ coordinateLineProjection R)
  (s : Spec (.of B) ⟶ Y) (hs : s ≫ p = coordinateMark R B z)
  (H : IsPullback s (𝟙 (Spec (.of B))) p (coordinateMark R B z))

/-- The actual marked coordinate survives arbitrary whole-scheme base change. -/
theorem compactificationMarkedDivisorFrame_pullback_coordinate {W : Scheme.{u}}
    (a : W ⟶ pullback (j ≫ q) (s ≫ j ≫ q)) :
    (Scheme.Modules.framePullback a
      (compactificationMarkedDivisorFrame R B z q j p hq s hs H)).hom.app ⊤
        (pullbackGlobalSections a _
          (pullbackGlobalSections (markedProductMap q j s)
            (divisorSheaf (compactificationGraph q j).ker)
            (divisorSheafGlobalSection (compactificationGraph q j).ker))) =
      a.appTop (markedGraphCoordinate R B z q j p hq s hs) := by
  rw [Scheme.Modules.framePullback_coordinate,
    compactificationMarkedDivisorFrame_coordinate]

/-- Specialization at an actual `Spec K` mark uses its exact ring map and preserves the sign. -/
theorem compactificationMarkedDivisorFrame_spec_coordinate (K : Type u) [Field K]
    (a : Spec (.of K) ⟶ pullback (j ≫ q) (s ≫ j ≫ q)) :
    (Scheme.ΓSpecIso (.of K)).hom
      ((Scheme.Modules.framePullback a
        (compactificationMarkedDivisorFrame R B z q j p hq s hs H)).hom.app ⊤
          (pullbackGlobalSections a _
            (pullbackGlobalSections (markedProductMap q j s)
              (divisorSheaf (compactificationGraph q j).ker)
              (divisorSheafGlobalSection (compactificationGraph q j).ker)))) =
      (Scheme.ΓSpecIso (.of K)).hom
        (a.appTop (markedGraphCoordinate R B z q j p hq s hs)) := by
  rw [compactificationMarkedDivisorFrame_pullback_coordinate]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
