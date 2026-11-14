/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.PerfectMayerVietoris
public import Colib.AlgebraicGeometry.KTheory.PerfectQcqsScalarBoundary
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedConeRestriction
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedConeAdditivity

/-! # The original Mayer–Vietoris boundary of a chart scalar -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.PerfectMayerVietoris

variable {V X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace V]
  [QuasiSeparatedSpace V] (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  [CompactSpace T.toScheme] [CompactSpace (j ⁻¹ᵁ T).toScheme]
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

attribute [local instance] HasDerivedCategory.standard

set_option quotPrecheck false in
local notation "U" => Scheme.Opens.toScheme (j ⁻¹ᵁ T)
local notation "WU" => RingedSpace.perfectComplexesWaldhausen
  (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace U))
local notation "WV" => RingedSpace.perfectComplexesWaldhausen V.toRingedSpace
local notation "WX" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "Res" => perfectComplexesRestrictOpenImmersion j
local notation "Perf" => ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))

omit [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace T.toScheme] in
/-- A supported global cone with a scalar chart comparison computes the actual MV boundary.
The conclusion uses the unmodified two-open boundary and the literal target-minus-source sign. -/
theorem connectingHom_scalarUnit_of_cone
    {F G : Perf ⥤ Perf} (α : F ⟶ G)
    (hα : ∀ K : Perf, (perfectOpenWeakWaldhausen T.ι).weq (α.app K))
    (hC : IsExact (WX).cof (WX).weq (perfectSupportedWaldhausen T.ι).cof
      (perfectSupportedWaldhausen T.ι).weq (perfectSupportedTransformationCone T.ι α hα))
    (hF : IsExact (WX).cof (WX).weq (WX).cof (WX).weq F)
    (hG : IsExact (WX).cof (WX).weq (WX).cof (WX).weq G)
    (r : Γ(V, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : (j ⁻¹ᵁ T).ι.appTop r = ↑q)
    (i : F ⋙ Res ≅ Res) (k : G ⋙ Res ≅ Res)
    (h : Functor.whiskerRight α Res ≫ k.hom =
      i.hom ≫ Functor.whiskerLeft Res (perfectGlobalScalar V r))
    (n : ℕ) (a : (WX).K n) :
    connectingHom j T hcover n
        (originalKSelfTrackOperation WV WU (perfectFlatUnitHomotopy (j ⁻¹ᵁ T).ι q) n
          (KMap (perfectComplexesRestrictOpenImmersion_isExact j) n a)) =
      KMap hG n a * (KMap hF n a)⁻¹ := by
  let y := originalKSelfTrackOperation WV WU (perfectFlatUnitHomotopy (j ⁻¹ᵁ T).ι q) n
    (KMap (perfectComplexesRestrictOpenImmersion_isExact j) n a)
  have hs : lowerBoundary j T hcover n y = KMap hC n a := by
    apply (perfectSupportedExcisionKEquiv j T hcover n).injective
    change (perfectSupportedExcisionKEquiv j T hcover n)
        ((perfectSupportedExcisionKEquiv j T hcover n).symm
          (perfectQcqsConnectingHom (j ⁻¹ᵁ T).ι n y)) =
      perfectSupportedKRestrict j T n (KMap hC n a)
    rw [MulEquiv.apply_symm_apply]
    exact (DFunLike.congr_fun
      (perfectQcqsConnectingHom_comp_scalarUnitOperation (j ⁻¹ᵁ T).ι r q hq n)
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) n a)).trans
      (DFunLike.congr_fun
        (perfectSupportedKRestrict_comp_transformationCone j T r q hq α hα hC i k h n) a).symm
  change perfectSupportedKMap T.ι n (lowerBoundary j T hcover n y) = _
  rw [hs]
  exact perfectSupportedTransformationCone_KMap_forget T.ι α hF hG hα hC n a

end AlgebraicGeometry.Scheme.Modules.PerfectMayerVietoris
