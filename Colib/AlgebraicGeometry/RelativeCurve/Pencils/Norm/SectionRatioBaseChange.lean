/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Finite.Norm.GlobalSections
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.SectionCoefficient

/-!
# Source change of the original section norm equation

The determinant norm and both original section ratios restrict along the
same actual Cartesian square, including on an integral source component.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Ample Stacks.Divisors Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- The original norm equation survives the literal preimage of the good
domain, using the same pulled sections and the original pullback of the unit. -/
theorem sectionNormRatio_morphismRestrict {X Y X' Y' P : Scheme.{u}}
    (f : X ⟶ Y) [IsFiniteLocallyFree f] (f' : X' ⟶ Y') [IsFiniteLocallyFree f']
    (i : X' ⟶ X) (j : Y' ⟶ Y) (H : IsPullback i f' f j) (κ : Y ⟶ P)
    (L : X.Modules) [IsInvertibleModule X L] (M : P.Modules) [IsInvertibleModule P M]
    (a₁ b₁ : Γ(L, ⊤)) (a₂ b₂ : Γ(M, ⊤)) (U : Y.Opens) (r : Γ(Y, U))
    (ha₁ : zeroScheme (pullback f U.ι) ((Modules.pullback (pullback.fst f U.ι)).obj L)
      (pullbackGlobalSections (pullback.fst f U.ι) L a₁) = ⊤)
    (ha₂ : zeroScheme U.toScheme ((Modules.pullback (U.ι ≫ κ)).obj M)
      (pullbackGlobalSections (U.ι ≫ κ) M a₂) = ⊤) :
    letI : IsFiniteLocallyFree (pullback.snd f U.ι) :=
      isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback f U.ι) inferInstance
    normTop (pullback.snd f U.ι)
        (sectionRatioCoefficient _ (pullbackGlobalSections (pullback.fst f U.ι) L a₁)
          (pullbackGlobalSections (pullback.fst f U.ι) L b₁) ha₁) * U.topIso.inv r =
      sectionRatioCoefficient _ (pullbackGlobalSections (U.ι ≫ κ) M a₂)
        (pullbackGlobalSections (U.ι ≫ κ) M b₂) ha₂ →
    let V := j ⁻¹ᵁ U
    let v₁ := pullback.fst f' V.ι
    letI : IsFiniteLocallyFree (pullback.snd f' V.ι) :=
      isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback f' V.ι) inferInstance
    let L' := (Modules.pullback i).obj L
    let M' := (Modules.pullback (j ≫ κ)).obj M
    let a₁' := pullbackGlobalSections i L a₁
    let b₁' := pullbackGlobalSections i L b₁
    let a₂' := pullbackGlobalSections (j ≫ κ) M a₂
    let b₂' := pullbackGlobalSections (j ≫ κ) M b₂
    ∃ (ha₁' : zeroScheme _ ((Modules.pullback v₁).obj L')
        (pullbackGlobalSections v₁ L' a₁') = ⊤)
      (ha₂' : zeroScheme _ ((Modules.pullback V.ι).obj M')
        (pullbackGlobalSections V.ι M' a₂') = ⊤),
      normTop (pullback.snd f' V.ι)
          (sectionRatioCoefficient _ (pullbackGlobalSections v₁ L' a₁')
            (pullbackGlobalSections v₁ L' b₁') ha₁') * V.topIso.inv (j.app U r) =
        sectionRatioCoefficient _ (pullbackGlobalSections V.ι M' a₂')
          (pullbackGlobalSections V.ι M' b₂') ha₂' := by
  dsimp only
  intro hnorm
  let V := j ⁻¹ᵁ U
  let u := j ∣_ U
  let fU := pullback.snd f U.ι
  let fV := pullback.snd f' V.ι
  let v₁ := pullback.fst f' V.ι
  let i₁ := pullback.fst f U.ι
  have hu : u ≫ U.ι = V.ι ≫ j := morphismRestrict_ι j U
  have houter : IsPullback (v₁ ≫ i) fV f (V.ι ≫ j) :=
    (IsPullback.of_hasPullback f' V.ι).paste_horiz H
  have hk : (v₁ ≫ i) ≫ f = (fV ≫ u) ≫ U.ι := by
    rw [Category.assoc fV u U.ι, hu]
    exact houter.w
  let k := pullback.lift (v₁ ≫ i) (fV ≫ u) hk
  have hk₁ : k ≫ i₁ = v₁ ≫ i := pullback.lift_fst _ _ _
  have hk₂ : k ≫ fU = fV ≫ u := pullback.lift_snd _ _ _
  have hcart : IsPullback k fV fU u :=
    (show IsPullback (k ≫ i₁) fV f (u ≫ U.ι) by rwa [hk₁, hu]).of_right
      hk₂ (IsPullback.of_hasPullback f U.ι)
  have hv : V.ι ≫ (j ≫ κ) = u ≫ (U.ι ≫ κ) := by
    simp only [← Category.assoc, hu]
  let ha₁' := zeroScheme_pullbackSquare_eq_top i i₁ v₁ k hk₁.symm L a₁ ha₁
  let ha₂' := zeroScheme_pullbackSquare_eq_top (j ≫ κ) (U.ι ≫ κ) V.ι u hv M a₂ ha₂
  refine ⟨ha₁', ha₂', ?_⟩
  have h₁ := sectionRatioCoefficient_appTop_of_pullbackSquare i i₁ v₁ k hk₁.symm
    L a₁ b₁ ha₁ ha₁'
  have h₂ := sectionRatioCoefficient_appTop_of_pullbackSquare (j ≫ κ) (U.ι ≫ κ) V.ι u hv
    M a₂ b₂ ha₂ ha₂'
  have hTop : u.appTop = U.topIso.hom ≫ j.app U ≫ V.topIso.inv := by
    have h := j.resLE_app_top (U := U) (V := j ⁻¹ᵁ U) le_rfl
    change (j.resLE U (j ⁻¹ᵁ U) le_rfl).appTop = _ at h
    rw [Hom.resLE_eq_morphismRestrict, Hom.appLE_eq_app] at h
    exact h
  have hR : V.topIso.inv (j.app U r) = u.appTop (U.topIso.inv r) := by
    rw [hTop, CommRingCat.comp_apply, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  let : IsFiniteLocallyFree fU := isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f U.ι) inferInstance
  let : IsFiniteLocallyFree fV := isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f' V.ι) inferInstance
  rw [← h₁, ← h₂, hR, normTop_appTop_of_isPullback fU fV k u hcart, ← map_mul, hnorm]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
