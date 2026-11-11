/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.SourceChangedMatching
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.BoundaryCoordinateUnit
public import Colib.AlgebraicGeometry.Divisors.FrameTransport

/-!
# The actual scalar unit on the changed whole boundary

The original whole-boundary graph frame is transported through the actual
commuting boundary square. Its canonical coordinate is the literal pullback of
the original scalar. If the changed boundary misses the graph, its zero ideal
is the unit ideal and multiplication by that exact scalar is an isomorphism.
No separately chosen unit, normalization or scalar equality is an input.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {X X' Z Z' : Scheme.{u}} (g : X' ⟶ X) (i : Z ⟶ X)
  (i' : Z' ⟶ X') (β : Z' ⟶ Z) (h : i' ≫ g = β ≫ i)

/-- The actual original frame transported along the two paths of the full square. -/
def sourceChangedBoundaryFrame (F : X.Modules)
    (e : (Modules.pullback i).obj F ≅ SheafOfModules.unit Z.ringCatSheaf) :
    (Modules.pullback i').obj ((Modules.pullback g).obj F) ≅
      SheafOfModules.unit Z'.ringCatSheaf :=
  boundaryPullbackSquareIso g i i' β h F ≪≫ Modules.framePullback β e

/-- Its canonical coordinate is the actual scalar restriction along beta. -/
theorem sourceChangedBoundaryFrame_coordinate (F : X.Modules)
    (e : (Modules.pullback i).obj F ≅ SheafOfModules.unit Z.ringCatSheaf)
    (s : Γ(F, ⊤)) :
    (sourceChangedBoundaryFrame g i i' β h F e).hom.app ⊤
      (pullbackGlobalSections i' _ (pullbackGlobalSections g F s)) =
        β.appTop (e.hom.app ⊤ (pullbackGlobalSections i F s)) := by
  change (Modules.framePullback β e).hom.app ⊤
    ((boundaryPullbackSquareIso g i i' β h F).hom.app ⊤
      (pullbackGlobalSections i' _ (pullbackGlobalSections g F s))) = _
  rw [boundaryPullbackSquareIso_section, Modules.framePullback_coordinate]

variable (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
  (e : (Modules.pullback i).obj (divisorSheaf D) ≅ SheafOfModules.unit Z.ringCatSheaf)
  (hdisj : Disjoint (Set.range (i' ≫ g)) (D.support : Set X))

/-- The literal original graph coordinate has no zeros on the entire changed boundary. -/
theorem zeroScheme_sourceChangedCoordinate_eq_top :
    zeroScheme Z' (SheafOfModules.unit Z'.ringCatSheaf)
      (β.appTop (e.hom.app ⊤
        (pullbackGlobalSections i (divisorSheaf D) (divisorSheafGlobalSection D)))) = ⊤ := by
  rw [← sourceChangedBoundaryFrame_coordinate g i i' β h (divisorSheaf D) e
      (divisorSheafGlobalSection D), zeroScheme_congr_iso,
    zeroScheme_pullback, zeroScheme_pullback, zeroScheme_canonicalSection,
    ← IdealSheafData.comap_comp]
  exact divisor_comap_eq_top_of_disjoint D (i' ≫ g) hdisj

/-- The actual scalar for the second correction, with invertibility derived from
its whole zero ideal rather than assumed. -/
def sourceChangedCoordinateUnit :
    SheafOfModules.unit Z'.ringCatSheaf ≅ SheafOfModules.unit Z'.ringCatSheaf := by
  let c := β.appTop (e.hom.app ⊤
    (pullbackGlobalSections i (divisorSheaf D) (divisorSheafGlobalSection D)))
  letI := isIso_sectionUnitHom_of_zeroScheme_eq_top _ c
    (zeroScheme_sourceChangedCoordinate_eq_top g i i' β h D e hdisj)
  exact asIso (sectionUnitHom _ c)

@[simp]
theorem sourceChangedCoordinateUnit_coordinate :
    (sourceChangedCoordinateUnit g i i' β h D e hdisj).hom.app ⊤ 1 =
      β.appTop (e.hom.app ⊤
        (pullbackGlobalSections i (divisorSheaf D) (divisorSheafGlobalSection D))) :=
  sectionUnitHom_app_one _ _

end AlgebraicGeometry.Scheme.RelativeCurvePencil
