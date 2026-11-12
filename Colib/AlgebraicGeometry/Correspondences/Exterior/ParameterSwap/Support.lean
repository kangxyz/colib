/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.PrimeSupport

/-!
# Full supports of iterated parameter exterior products

The native support isomorphism after the first exterior product extends
over the next parameter. Its inclusion retains both old projections
and the literal second parameter on each side.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y T V : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

local notation "W" => integralComponentAt z
local notation "Xₜ" => SmoothSite.product X T
local notation "Yₜ" => SmoothSite.product Y T
local notation "Xₜᵥ" => SmoothSite.product Xₜ V
local notation "Yₜᵥ" => SmoothSite.product Yₜ V
local notation "zₜ" => nativeExteriorPoint X Y T z hz
local notation "Wₜ" => integralComponentAt zₜ
local notation "b₀" => exteriorSupportSourceProjection X Y W ≫ X.hom
set_option quotPrecheck false in
local notation "bₜ" => exteriorSupportSourceProjection Xₜ Yₜ Wₜ ≫ (Xₜ).hom
local notation "b₁" => pullback.fst b₀ T.hom ≫ b₀
local notation "Pₜᵥ" => pullback (C := Scheme) b₁ V.hom
local notation "E" => nativeExteriorSupportIso X Y T z hz

/-- The second native exterior support is the full iterated product of the
original closed support and the two parameters. -/
def nativeExteriorIteratedSupportIso :
    Pₜᵥ ≅ exteriorIdentitySupport Xₜ Yₜ V Wₜ := by
  have hbase : (E).hom ≫ bₜ = b₁ := by
    have he : (E).hom ≫ exteriorSupportSourceProjection Xₜ Yₜ Wₜ =
        exteriorIdentitySource X Y T W :=
      nativeExteriorSupportIso_hom_source X Y T z hz
    rw [← Category.assoc, he]
    change exteriorIdentitySource X Y T W ≫ pullback.fst X.hom T.hom ≫ X.hom = _
    rw [exteriorIdentitySource_fst_assoc]
    simp only [exteriorSupportSourceProjection, Category.assoc]
  have h₁ : b₁ ≫ 𝟙 (Spec (.of k)) = (E).hom ≫ bₜ :=
    (Category.comp_id b₁).trans hbase.symm
  have h₂ : V.hom ≫ 𝟙 (Spec (.of k)) = 𝟙 V.left ≫ V.hom :=
    (Category.comp_id V.hom).trans (Category.id_comp V.hom).symm
  let e : Pₜᵥ ⟶ exteriorIdentitySupport Xₜ Yₜ V Wₜ :=
    pullback.map b₁ V.hom bₜ V.hom (E).hom (𝟙 V.left) (𝟙 (Spec (.of k))) h₁ h₂
  let : IsIso (𝟙 V.left) := (Iso.refl V.left).isIso_hom
  let : IsIso (𝟙 (Spec (.of k))) := (Iso.refl (Spec (.of k))).isIso_hom
  have : IsIso e :=
    pullback.map_isIso b₁ V.hom bₜ V.hom (E).hom (𝟙 V.left) (𝟙 (Spec (.of k))) h₁ h₂
  exact asIso e

local notation "E₂" => nativeExteriorIteratedSupportIso X Y T V z hz

@[reassoc (attr := simp)]
theorem nativeExteriorIteratedSupportIso_hom_fst :
    (E₂).hom ≫ pullback.fst bₜ V.hom = pullback.fst b₁ V.hom ≫ (E).hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem nativeExteriorIteratedSupportIso_hom_snd :
    (E₂).hom ≫ pullback.snd bₜ V.hom = pullback.snd b₁ V.hom :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The original iterated product maps to the literal ambient of the twice
extended correspondence. -/
def nativeExteriorIteratedInclusion :
    Pₜᵥ ⟶ pullback (C := Scheme) (Xₜᵥ).hom (Yₜᵥ).hom :=
  (E₂).hom ≫ exteriorIdentityInclusion Xₜ Yₜ V Wₜ

local notation "I" => nativeExteriorIteratedInclusion X Y T V z hz

/-- The old source product is retained by the actual iterated support inclusion. -/
@[reassoc (attr := simp)]
theorem nativeExteriorIteratedInclusion_source_fst :
    I ≫ pullback.fst (Xₜᵥ).hom (Yₜᵥ).hom ≫ pullback.fst (Xₜ).hom V.hom =
      pullback.fst b₁ V.hom ≫ exteriorIdentitySource X Y T W := by
  have h : (E).hom ≫ exteriorSupportSourceProjection Xₜ Yₜ Wₜ =
      exteriorIdentitySource X Y T W :=
    nativeExteriorSupportIso_hom_source X Y T z hz
  simp only [nativeExteriorIteratedInclusion, Category.assoc, exteriorIdentityInclusion_fst_assoc,
    exteriorIdentitySource_fst, nativeExteriorIteratedSupportIso_hom_fst_assoc, h]

/-- The old target product is retained by the actual iterated support inclusion. -/
@[reassoc (attr := simp)]
theorem nativeExteriorIteratedInclusion_target_fst :
    I ≫ pullback.snd (Xₜᵥ).hom (Yₜᵥ).hom ≫ pullback.fst (Yₜ).hom V.hom =
      pullback.fst b₁ V.hom ≫ exteriorIdentityTarget X Y T W := by
  have h : (E).hom ≫ exteriorSupportTargetProjection Xₜ Yₜ Wₜ =
      exteriorIdentityTarget X Y T W :=
    nativeExteriorSupportIso_hom_target X Y T z hz
  simp only [nativeExteriorIteratedInclusion, Category.assoc, exteriorIdentityInclusion_snd_assoc,
    exteriorIdentityTarget_fst, nativeExteriorIteratedSupportIso_hom_fst_assoc, h]

/-- The new source parameter is the literal second product projection. -/
@[reassoc (attr := simp)]
theorem nativeExteriorIteratedInclusion_source_snd :
    I ≫ pullback.fst (Xₜᵥ).hom (Yₜᵥ).hom ≫ pullback.snd (Xₜ).hom V.hom =
      pullback.snd b₁ V.hom := by
  simp only [nativeExteriorIteratedInclusion, Category.assoc, exteriorIdentityInclusion_fst_assoc,
    exteriorIdentitySource_snd, nativeExteriorIteratedSupportIso_hom_snd]

/-- The new target parameter is the same literal product projection. -/
@[reassoc (attr := simp)]
theorem nativeExteriorIteratedInclusion_target_snd :
    I ≫ pullback.snd (Xₜᵥ).hom (Yₜᵥ).hom ≫ pullback.snd (Yₜ).hom V.hom =
      pullback.snd b₁ V.hom := by
  simp only [nativeExteriorIteratedInclusion, Category.assoc, exteriorIdentityInclusion_snd_assoc,
    exteriorIdentityTarget_snd, nativeExteriorIteratedSupportIso_hom_snd]

end Stacks.Chow
