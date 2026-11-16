/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectSupportedConeRestriction
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedExcision
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCone

/-! # Restriction of the supported cone on native K-groups -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X V : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens)
local notation "P" => RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
local notation "Perf" => ObjectProperty.FullSubcategory P
local notation "W" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "Res" => perfectComplexesRestrictOpenImmersion j


variable (r : Γ(V, ⊤)) (q : (Γ((j ⁻¹ᵁ T).toScheme, ⊤))ˣ)
variable (hq : (j ⁻¹ᵁ T).ι.appTop r = ↑q)

theorem perfectSupportedKRestrict_comp_transformationCone
    {F G : Perf ⥤ Perf} (α : NatTrans F G)
    (hα : ∀ K : Perf, (perfectOpenWeakWaldhausen T.ι).weq (NatTrans.app α K))
    (hC : IsExact (W).cof (W).weq (perfectSupportedWaldhausen T.ι).cof
      (perfectSupportedWaldhausen T.ι).weq
      (@perfectSupportedTransformationCone X T.toScheme T.ι inferInstance F G α hα))
    (i : F ⋙ Res ≅ Res) (k : G ⋙ Res ≅ Res)
    (h : Functor.whiskerRight α Res ≫ k.hom =
      i.hom ≫ Functor.whiskerLeft Res (perfectGlobalScalar V r))
    (n : ℕ) :
    (perfectSupportedKRestrict j T n).comp (KMap hC n) =
      (perfectSupportedScalarConeKMap (j ⁻¹ᵁ T).ι r q hq n).comp
        (KMap (perfectComplexesRestrictOpenImmersion_isExact j) n) := by
  unfold perfectSupportedKRestrict perfectSupportedScalarConeKMap
  rw [KMap_comp_KMap, KMap_comp_KMap]
  exact KMap_eq_of_iso _ _ (perfectSupportedConeRestrictScalarIso j T r q hq α hα i k h) n

end AlgebraicGeometry.Scheme.Modules
