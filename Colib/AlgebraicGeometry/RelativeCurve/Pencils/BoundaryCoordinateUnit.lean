/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.CanonicalBoundaryFrame
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeUnits

/-!
# The canonical boundary coordinate is a genuine unit off the graph

On a boundary disjoint from the actual divisor, the canonical section has no
zeros. Reading it in any specified frame therefore gives an actual invertible
endomorphism of the structure module. This produces the scalar used by the
second correction; invertibility is not an extra scalar hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {X Z : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
  (i : Z ⟶ X) (h : Disjoint (Set.range i) (D.support : Set X))
  (e : (Modules.pullback i).obj (divisorSheaf D) ≅ SheafOfModules.unit Z.ringCatSheaf)

/-- The specified coordinate, rather than an arbitrary replacement section, has
unit zero ideal on the entire boundary when that boundary misses the divisor. -/
theorem zeroScheme_boundaryCoordinate_eq_top :
    zeroScheme Z (SheafOfModules.unit Z.ringCatSheaf)
      (e.hom.app ⊤ (pullbackGlobalSections i (divisorSheaf D) (divisorSheafGlobalSection D))) =
        ⊤ := by
  rw [zeroScheme_congr_iso]
  exact canonicalSection_zeroScheme_on_disjoint_boundary D i h

/-- The actual unit automorphism determined by the prescribed canonical coordinate. -/
def boundaryCoordinateUnit :
    SheafOfModules.unit Z.ringCatSheaf ≅ SheafOfModules.unit Z.ringCatSheaf := by
  let s := e.hom.app ⊤
    (pullbackGlobalSections i (divisorSheaf D) (divisorSheafGlobalSection D))
  letI := isIso_sectionUnitHom_of_zeroScheme_eq_top _ s
    (zeroScheme_boundaryCoordinate_eq_top D i h e)
  exact asIso (sectionUnitHom _ s)

/-- The generated scalar unit has exactly the original canonical coordinate. -/
@[simp]
theorem boundaryCoordinateUnit_coordinate :
    (boundaryCoordinateUnit D i h e).hom.app ⊤ 1 =
      e.hom.app ⊤ (pullbackGlobalSections i (divisorSheaf D) (divisorSheafGlobalSection D)) :=
  sectionUnitHom_app_one _ _

end AlgebraicGeometry.Scheme.RelativeCurvePencil
