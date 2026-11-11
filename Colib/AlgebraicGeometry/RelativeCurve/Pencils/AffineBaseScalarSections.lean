/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.AffineBaseNormalizedSections
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.ScalarBoundarySections

/-!
# Actual scalar pairs after affine base shrinking

The whole finite boundary produces the coefficient-power frames on one affine
base neighbourhood. Pulling back the original scalar automorphism preserves its
literal coordinate, and coherent Serre produces the two scalar-normalized
sections there. No coefficient frame or prescribed section is an input.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Ample Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

attribute [local instance]
  Stacks.OpensSheafification.hasSheafifyOpens
  Stacks.OpensSheafification.wEqualsLocallyBijectiveOpens

/-- The actual pullback of a structure-module automorphism. -/
def unitAutomorphismPullback {Z Z' : Scheme.{u}} (β : Z' ⟶ Z)
    (E : SheafOfModules.unit Z.ringCatSheaf ≅ SheafOfModules.unit Z.ringCatSheaf) :
    SheafOfModules.unit Z'.ringCatSheaf ≅ SheafOfModules.unit Z'.ringCatSheaf :=
  (Modules.pullbackUnitIso β).symm ≪≫ Modules.framePullback β E

/-- Pullback preserves the exact coordinate of the original scalar automorphism. -/
theorem unitAutomorphismPullback_coordinate {Z Z' : Scheme.{u}} (β : Z' ⟶ Z)
    (E : SheafOfModules.unit Z.ringCatSheaf ≅ SheafOfModules.unit Z.ringCatSheaf) :
    (unitAutomorphismPullback β E).hom.app ⊤ 1 = β.appTop (E.hom.app ⊤ 1) := by
  have h := SectionsEqualizer.pullbackUnitIso_unit β (1 : Γ(Z, ⊤))
  have h' := congrArg ((Modules.pullbackUnitIso β).inv.app ⊤) h
  have hc := congrArg (fun m => m.app ⊤
      (pullbackGlobalSections β (SheafOfModules.unit Z.ringCatSheaf) (1 : Γ(Z, ⊤))))
    (Modules.pullbackUnitIso β).hom_inv_id
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    CategoryTheory.comp_apply, CategoryTheory.id_apply] at hc
  rw [hc, map_one] at h'
  change (Modules.framePullback β E).hom.app ⊤ ((Modules.pullbackUnitIso β).inv.app ⊤ 1) = _
  rw [← h', Modules.framePullback_coordinate]

/-- Produce the actual second pair on a whole affine base neighbourhood. Both
zero schemes on the complete boundary are empty, and the scalar is the literal
restriction of the original prescribed unit. -/
theorem exists_affineBase_scalar_sections {S X Z : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [IsLocallyNoetherian S] [IsProper f]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsFinite (i ≫ f)]
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)
    (E : SheafOfModules.unit Z.ringCatSheaf ≅ SheafOfModules.unit Z.ringCatSheaf) (x : S) :
    ∃ U : S.affineOpens, x ∈ U.1 ∧
      let LU := (Modules.pullback (f ⁻¹ᵁ U.1).ι).obj L
      let iU := baseRestrictedBoundary f i U.1
      let β := (i ⁻¹ᵁ (f ⁻¹ᵁ U.1)).ι
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ a b : Γ(tensorPowModule (f ⁻¹ᵁ U.1).toScheme LU (n : ℤ), ⊤),
          pullbackGlobalSections iU _ a =
            β.appTop (E.hom.app ⊤ 1) • pullbackGlobalSections iU _ b ∧
          zeroScheme (i ⁻¹ᵁ (f ⁻¹ᵁ U.1)).toScheme
            ((Modules.pullback iU).obj (tensorPowModule (f ⁻¹ᵁ U.1).toScheme LU (n : ℤ)))
            (pullbackGlobalSections iU _ a) = ⊤ ∧
          zeroScheme (i ⁻¹ᵁ (f ⁻¹ᵁ U.1)).toScheme
            ((Modules.pullback iU).obj (tensorPowModule (f ⁻¹ᵁ U.1).toScheme LU (n : ℤ)))
            (pullbackGlobalSections iU _ b) = ⊤ := by
  obtain ⟨U, hx, ⟨eL⟩⟩ := exists_affine_wholeFiniteBoundary_frame (i ≫ f)
    ((Modules.pullback i).obj L) x
  rw [Scheme.Hom.comp_preimage] at eL
  let g := (f ⁻¹ᵁ U.1).ι
  let β := (i ⁻¹ᵁ (f ⁻¹ᵁ U.1)).ι
  let iU := baseRestrictedBoundary f i U.1
  let LU := (Modules.pullback g).obj L
  letI : IsAffine U.1.toScheme := U.2
  letI : IsProper (f ∣_ U.1) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U.1).flip inferInstance
  letI : IsClosedImmersion iU :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict i (f ⁻¹ᵁ U.1)).flip
      inferInstance
  letI : IsAffineHom g :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U.1) inferInstance
  have hLU : IsAmple (f ⁻¹ᵁ U.1).toScheme LU :=
    Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom g L hL
  let eLU : (Modules.pullback iU).obj LU ≅
      SheafOfModules.unit (i ⁻¹ᵁ (f ⁻¹ᵁ U.1)).toScheme.ringCatSheaf :=
    boundaryPullbackSquareIso g i iU β (morphismRestrict_ι i (f ⁻¹ᵁ U.1)) L ≪≫
      ((Modules.restrictFunctorIsoPullback β).app ((Modules.pullback i).obj L)).symm ≪≫ eL
  obtain ⟨N, hN⟩ := exists_eventually_scalar_boundary_sections (f ∣_ U.1) LU hLU iU
    (unitAutomorphismPullback β E)
  refine ⟨U, hx, N, fun n hn => ?_⟩
  obtain ⟨en⟩ := Stacks.AlgebraicGeometry.PicardBaseChange.isTrivial_pullback_tensorPower
    iU LU ⟨eLU⟩ (n : ℤ)
  obtain ⟨a, b, hab, ha, hb⟩ := hN n hn en
  rw [unitAutomorphismPullback_coordinate] at hab
  exact ⟨a, b, hab, ha, hb⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil
