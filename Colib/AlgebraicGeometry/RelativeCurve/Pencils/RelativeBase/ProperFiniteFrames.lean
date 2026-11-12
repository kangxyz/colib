/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Compactification.Retained.BoundaryPrescribedScheme
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.FiniteFrames
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # A frame on a full proper boundary near a finite fiber

Adapted from `Motivic/Aglib/AlgebraicGeometry/Modules/Invertible/Frames/`
`ProperFiniteFiber.lean` at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Stacks.Ample

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- A proper boundary with finite fiber has a full frame and is finite over
one actual base neighborhood. -/
theorem exists_base_open_finite_and_frame {D S : Scheme.{u}} (f : D ⟶ S) [IsProper f]
    (x : S) (hx : (f ⁻¹' {x}).Finite) (L : D.Modules) [IsInvertibleModule D L] :
    ∃ V : S.Opens, x ∈ V ∧ IsFinite (f ∣_ V) ∧
      Nonempty (L.restrict (f ⁻¹ᵁ V).ι ≅
        SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf) := by
  obtain ⟨U, hxU, hfin⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton f x hx
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hxU
  let : IsFinite (f ∣_ U) := hfin
  let : IsAffine W.toScheme := hW
  let : IsFinite (f ∣_ W) := Scheme.RelativeCurve.finite_morphismRestrict_of_le f hWU
  let E := f ⁻¹ᵁ W
  let L' := (Modules.pullback E.ι).obj L
  let : IsInvertibleModule E.toScheme L' := inferInstance
  let y : W.toScheme := ⟨x, hxW⟩
  obtain ⟨T, hyT, ⟨e⟩⟩ := exists_finiteTargetFrame_around_finite (f ∣_ W)
    L' {y} (Set.finite_singleton y)
  let V := W.ι ''ᵁ T
  let Z := (f ∣_ W) ⁻¹ᵁ T
  let j := Z.ι ≫ E.ι
  have hxV : x ∈ V := ⟨y, hyT (Set.mem_singleton y), rfl⟩
  have hVW : V ≤ W := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  have hj : j.opensRange = f ⁻¹ᵁ V := by
    rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]
    exact image_morphismRestrict_preimage f W T
  let e' : L.restrict j ≅ SheafOfModules.unit Z.toScheme.ringCatSheaf :=
    (Modules.restrictFunctorComp Z.ι E.ι).app L ≪≫
      (Modules.restrictFunctor Z.ι).mapIso ((Modules.restrictFunctorIsoPullback E.ι).app L) ≪≫ e
  have hframe : Nonempty (L.restrict j.opensRange.ι ≅
      SheafOfModules.unit j.opensRange.toScheme.ringCatSheaf) :=
    ⟨Stacks.SheafOfModules.restrictIsoUnitOfIsoOver L j.isoOpensRange
      j.isoOpensRange_hom_ι e'⟩
  rw [hj] at hframe
  exact ⟨V, hxV, Scheme.RelativeCurve.finite_morphismRestrict_of_le f hVW, hframe⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
