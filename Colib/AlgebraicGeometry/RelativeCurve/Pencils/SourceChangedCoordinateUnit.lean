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

include h hdisj in
/-- The literal original graph coordinate has no zeros on the entire changed boundary. -/
theorem zeroScheme_sourceChangedCoordinate_eq_top :
    zeroScheme Z' (SheafOfModules.unit Z'.ringCatSheaf)
      (β.appTop (e.hom.app ⊤
        (pullbackGlobalSections i (divisorSheaf D) (divisorSheafGlobalSection D)))) = ⊤ := by
  let F := divisorSheaf D
  let s := divisorSheafGlobalSection D
  let s' := pullbackGlobalSections g F s
  let e' := sourceChangedBoundaryFrame g i i' β h F e
  have h₁ := sourceChangedBoundaryFrame_coordinate g i i' β h F e s
  have h₂ := zeroScheme_congr_iso e' (pullbackGlobalSections i' _ s')
  have h₃ := zeroScheme_pullback i' ((Modules.pullback g).obj F) s'
  have h₄ := (zeroScheme_pullback g F s).trans
    (congrArg (fun I : X.IdealSheafData => I.comap g) (zeroScheme_canonicalSection D))
  have h₅ := (IdealSheafData.comap_comp D i' g).symm.trans
    (divisor_comap_eq_top_of_disjoint D (i' ≫ g) hdisj)
  exact (congrArg (fun t : Γ(Z', ⊤) => zeroScheme Z'
    (SheafOfModules.unit Z'.ringCatSheaf) t) h₁.symm).trans
    (h₂.trans (h₃.trans
      ((congrArg (fun I : X'.IdealSheafData => I.comap i') h₄).trans h₅)))

/-- The actual scalar for the second correction, with invertibility derived from
its whole zero ideal rather than assumed. -/
def sourceChangedCoordinateUnit :
    SheafOfModules.unit Z'.ringCatSheaf ≅ SheafOfModules.unit Z'.ringCatSheaf := by
  let c : Γ(Z', ⊤) := β.appTop (e.hom.app ⊤
    (pullbackGlobalSections i (divisorSheaf D) (divisorSheafGlobalSection D)))
  exact (@frameOfZeroSchemeTop Z' (SheafOfModules.unit Z'.ringCatSheaf)
    (Stacks.Ample.isInvertibleModule_unit Z') c
    (zeroScheme_sourceChangedCoordinate_eq_top g i i' β h D e hdisj)).symm

@[simp]
theorem sourceChangedCoordinateUnit_coordinate :
    Modules.Hom.app (X := Z') (sourceChangedCoordinateUnit g i i' β h D e hdisj).hom ⊤
      (1 : Γ(Z', ⊤)) =
      β.appTop (e.hom.app ⊤
        (pullbackGlobalSections i (divisorSheaf D) (divisorSheafGlobalSection D))) :=
  sectionUnitHom_app_one _ _

end AlgebraicGeometry.Scheme.RelativeCurvePencil
