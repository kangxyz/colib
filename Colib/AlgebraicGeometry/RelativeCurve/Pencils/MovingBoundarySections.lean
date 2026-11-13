/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.BoundaryFrameCoordinates
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedFamilyRestriction

/-!
# The infinity condition for a graph pencil

The graph section has coordinate one on the infinity summand in its
canonical frame. After Serre normalization on the full boundary, the
graph-times-pole and the numerator agree on infinity.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Moving/OneSidedBoundary.lean`
and `Motivic/Aglib/AlgebraicGeometry/Moving/OneSidedPencil.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {C D Z : Scheme.{u}} (d : D ⟶ C) (z : Z ⟶ C)
  (F T : C.Modules) (σ : Γ(F, ⊤)) (a : Γ(tensorModules F T, ⊤)) (b : Γ(T, ⊤))
  (e : (Modules.pullback (coprod.desc d z)).obj F ≅ SheafOfModules.unit (D ⨿ Z).ringCatSheaf)

/-- The normalized graph-times-pole and the numerator have identical infinity values. -/
theorem graphPole_infinity_eq_of_normalization
    (hσ : (coprod.inl : D ⟶ D ⨿ Z).appTop
      (e.hom.app ⊤ (pullbackGlobalSections (coprod.desc d z) F σ)) = 1)
    (ha : (fixedFactorBoundaryIso (coprod.desc d z) F T e).hom.app ⊤
      (pullbackGlobalSections (coprod.desc d z) _ a) =
        pullbackGlobalSections (coprod.desc d z) _ b) :
    pullbackGlobalSections d _ (tensorSection F T ⊤ σ b) = pullbackGlobalSections d _ a := by
  let i := coprod.desc d z
  let l : D ⟶ D ⨿ Z := coprod.inl
  let M := tensorModules F T
  have h := graphPole_boundary_eq_coordinate_smul i F T e σ a b ha
  have h' := congrArg (pullbackGlobalSections l ((Modules.pullback i).obj M)) h
  rw [SectionsEqualizer.pullbackGlobalSections_smul, hσ, one_smul] at h'
  let e₁ := ((Modules.pullbackComp l i).hom.app M).app ⊤
  let e₂ := ((Modules.pullbackCongr (coprod.inl_desc d z)).app M).hom.app ⊤
  have hcomp (s : Γ(M, ⊤)) :
      e₂ (e₁ (pullbackGlobalSections l ((Modules.pullback i).obj M)
        (pullbackGlobalSections i M s))) = pullbackGlobalSections d M s := by
    dsimp only [e₁, e₂, l, i]
    rw [SectionsEqualizer.pullbackGlobalSections_comp]
    have hcongr {f g : D ⟶ C} (h : f = g) :
        ((Modules.pullbackCongr h).app M).hom.app ⊤ (pullbackGlobalSections f M s) =
          pullbackGlobalSections g M s := by
      subst g
      rfl
    exact hcongr (coprod.inl_desc d z)
  exact (hcomp _).symm.trans ((congrArg (fun s => e₂ (e₁ s)) h').trans (hcomp _))

/-- A section with unit zero ideal on the full boundary has unit zero ideal on
the whole infinity summand. -/
theorem zeroScheme_infinity_eq_top_of_boundary_zero
    (M : C.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property M]
    (s : Γ(M, ⊤))
    (hs : zeroScheme (D ⨿ Z) ((Modules.pullback (coprod.desc d z)).obj M)
      (pullbackGlobalSections (coprod.desc d z) M s) = ⊤) :
    zeroScheme D ((Modules.pullback d).obj M) (pullbackGlobalSections d M s) = ⊤ := by
  let l : D ⟶ D ⨿ Z := coprod.inl
  let I := zeroScheme C M s
  have hi : I.comap (coprod.desc d z) = ⊤ :=
    (Stacks.Divisors.zeroScheme_pullback (coprod.desc d z) M s).symm.trans hs
  have h := congrArg (fun J : (D ⨿ Z).IdealSheafData => J.comap l) hi
  rw [← IdealSheafData.comap_comp, show l ≫ coprod.desc d z = d from coprod.inl_desc d z,
    IdealSheafData.comap_top] at h
  exact (Stacks.Divisors.zeroScheme_pullback d M s).trans h

end AlgebraicGeometry.Scheme.RelativeCurvePencil
