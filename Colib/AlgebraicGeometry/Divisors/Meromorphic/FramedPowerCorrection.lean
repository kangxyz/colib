/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CommonNonvanishingRatioGeneric
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.TensorPowerRegularPullback
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.TensorPowerRegularGeneric
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalDifferenceBoundary

/-!
# The original framed tensor-root correction is a unit equal to one along the full boundary

The correcting rational function is the already constructed native ratio
`c / alpha(m^(k+1))`. Its ordinary unit representative is produced on the actual common
nonvanishing open. The original root frame and the original canonical Cartier-difference
frame are retained, including all boundary nilpotents.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules Stacks.Divisors
open Stacks.SheafOfModules (schemeTensorPower)

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry

variable {X B : Scheme.{u}} [IsIntegral X] (i : B ⟶ X)
  (D E : X.IdealSheafData) [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]
  (L : X.Modules) [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]

local instance framedCorrectionInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := hL.toAlgebraicGeometry

local instance framedCorrectionQuasicoherent (F : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property F] : F.IsQuasicoherent :=
  isQuasicoherent_of_isInvertible F

local instance framedCorrectionDifferenceInvertible :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf (differenceSheaf D E) :=
  isInvertible_differenceSheaf D E

local instance framedCorrectionDifferenceAGInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property (differenceSheaf D E) :=
  (isInvertible_differenceSheaf D E).toAlgebraicGeometry

local instance framedCorrectionPullbackInvertible :
    Stacks.SheafOfModules.IsInvertible B.presheaf B.ringCatIsSheaf ((pullback i).obj L) :=
  Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj i.toLRSHom.toShHom L

local instance framedCorrectionPullbackAGInvertible :
    SheafOfModules.IsInvertible B.presheaf (ringSheafCond B) ((pullback i).obj L) :=
  (framedCorrectionPullbackInvertible i L).toAlgebraicGeometry

local instance framedCorrectionMulCommutative :
    ∀ V, IsMulCommutative ((ringSheaf B).obj.obj V) :=
  fun V => inferInstanceAs (IsMulCommutative (B.presheaf.obj V))

local instance framedCorrectionTensorEquivalence :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
        (forget₂ CommRingCat RingCat) X.ringCatIsSheaf⟩).flip.obj L).IsEquivalence :=
  @Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor
    _ _ _ X.presheaf X.ringCatIsSheaf _ _ L hL

local instance framedCorrectionPowerInvertible (n : ℤ) :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (schemeTensorPower X L hL n) :=
  (Stacks.SheafOfModules.isInvertible_schemeTensorPower X L hL n).toAlgebraicGeometry

section GeneralTarget

variable (P : X.Modules)
  [hP : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf P]

local instance framedCorrectionTargetAGInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property P := hP.toAlgebraicGeometry

/-- Generic-target synthesis of the actual power correction from two original ordinary
representatives, retaining the specified root and target frames. -/
theorem exists_denseOpen_unit_framedPowerCorrection_of_regularRepresentative
    (k : ℕ) (α : schemeTensorPower X L hL (k + 1) ≅ P)
    (e : (pullback i).obj L ≅ SheafOfModules.unit (ringSheaf B))
    (τ : (pullback i).obj P ≅ SheafOfModules.unit B.ringCatSheaf)
    (hcompat : tensorPowerMap B e (k + 1) ≪≫ structureSheafTensorPowerIso B (k + 1) =
      (pullbackIntegerTensorPowerIso i L hL (k + 1)).symm ≪≫ (pullback i).mapIso α ≪≫ τ)
    (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s)
    (U : X.Opens) (hη : genericPoint X ∈ U) (hB : i ⁻¹ᵁ U = ⊤) (m : Γ(L, U))
    (hm : meromorphicGenericValue X L s = L.presheaf.germ U (genericPoint X) hη m)
    (hmB : Hom.app e.hom ⊤ (pullbackSectionHom i L U ⊤ hB.ge m) = (1 : Γ(B, ⊤)))
    (c : MeromorphicSection X.sheaf P) (hc : IsRegularMeromorphicSection X.sheaf P c)
    (V : X.Opens) (hηV : genericPoint X ∈ V) (hBV : (⊤ : B.Opens) ≤ i ⁻¹ᵁ V)
    (cV : Γ(P, V))
    (hcV : meromorphicGenericValue X P c = P.presheaf.germ V (genericPoint X) hηV cV)
    (hcB : τ.hom.app ⊤ (pullbackSectionHom i P V ⊤ hBV cV) = (1 : Γ(B, ⊤))) :
    ∃ (W : Stacks.Chow.DenseOpen X) (u : Γ(X, W.val)ˣ)
      (hBW : (⊤ : B.Opens) ≤ i ⁻¹ᵁ W.val),
      Units.map (Stacks.Chow.ofSectionRingHom X W).toMonoidHom u =
        tensorPowerCorrectionRatio X L P s hs k α c hc ∧
      i.appLE W.val ⊤ hBW u.val = (1 : Γ(B, ⊤)) := by
  let p : Γ(P, U) := Hom.app α.hom U (natTensorPowerRegularSection X L U m (k + 1))
  let t : MeromorphicSection X.sheaf P := mapMeromorphicSection
    (show X.Modules from schemeTensorPower X L hL (k + 1)) P α.hom
    (positiveTensorPowerMeromorphicSection X L s hs k).val
  have ht : IsRegularMeromorphicSection X.sheaf P t :=
    isRegularMeromorphicSection_mapMeromorphicSection
      (show X.Modules from schemeTensorPower X L hL (k + 1)) P α _
      (positiveTensorPowerMeromorphicSection X L s hs k).property
  have hp : meromorphicGenericValue X P t = P.presheaf.germ U (genericPoint X) hη p :=
    meromorphicGenericValue_rootImage_eq_germ_natTensorPowerRegularSection
      X L P s hs U hη m hm k α
  have hpB : Hom.app τ.hom ⊤ (pullbackSectionHom i P U ⊤ hB.ge p) = (1 : Γ(B, ⊤)) :=
    frame_rootImage_natTensorPowerRegularSection_boundary i L P (k + 1) α e τ
      hcompat U hB m hmB
  obtain ⟨W, u, hBW, _, hratio, hboundary⟩ :=
    exists_denseOpen_unit_eq_meromorphicSectionRatio_boundary_one P i U V hη hηV hB.ge hBV
      p cV c t hc ht hcV hp τ hpB hcB
  exact ⟨W, u, hBW, hratio, hboundary⟩

end GeneralTarget

/-- The canonical ordinary representative and its original boundary coordinate, packaged
only after both identities have been proved for the actual canonical section. -/
theorem exists_canonicalDifference_regularRepresentative_boundary_one
    (hD : ∀ y : B, i y ∉ D.support) (hE : ∀ y : B, i y ∉ E.support) :
    ∃ (V : X.Opens) (hηV : genericPoint X ∈ V) (hBV : (⊤ : B.Opens) ≤ i ⁻¹ᵁ V)
      (cV : Γ(differenceSheaf D E, V)),
      meromorphicGenericValue X (differenceSheaf D E) (canonicalDifferenceMeromorphicSection D E) =
        (differenceSheaf D E).presheaf.germ V (genericPoint X) hηV cV ∧
      (differenceSheafBoundaryIso i D E hD hE).hom.app ⊤
        (pullbackSectionHom i (differenceSheaf D E) V ⊤ hBV cV) = (1 : Γ(B, ⊤)) := by
  exact ⟨canonicalDifferenceRegularOpen E, genericPoint_mem_nonvanishingOpen_canonicalSection E,
    (preimage_canonicalDifferenceRegularOpen_eq_top i E hE).ge,
    canonicalDifferenceRegularSection D E,
    meromorphicGenericValue_canonicalDifference_eq_germ_regularSection D E,
    (congrArg ((differenceSheafBoundaryIso i D E hD hE).hom.app ⊤)
      (canonicalDifferenceBoundaryRegularSection_eq_pullback i D E hE).symm).trans
      (frame_canonicalDifferenceBoundaryRegularSection_eq_one i D E hD hE)⟩

/-- The exact correcting ratio of the specified framed root and original canonical Cartier
section has an actual ordinary unit representative equal to one on the full boundary. -/
@[colib_tag "COL-1066"]
theorem exists_denseOpen_unit_tensorPowerCorrectionRatio_boundary_one
    (hD : ∀ y : B, i y ∉ D.support) (hE : ∀ y : B, i y ∉ E.support)
    (k : ℕ) (α : schemeTensorPower X L hL (k + 1) ≅ differenceSheaf D E)
    (e : (pullback i).obj L ≅ SheafOfModules.unit (ringSheaf B))
    (hcompat : tensorPowerMap B e (k + 1) ≪≫ structureSheafTensorPowerIso B (k + 1) =
      (pullbackIntegerTensorPowerIso i L hL (k + 1)).symm ≪≫ (pullback i).mapIso α ≪≫
        differenceSheafBoundaryIso i D E hD hE)
    (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s)
    (U : X.Opens) (hη : genericPoint X ∈ U) (hB : i ⁻¹ᵁ U = ⊤) (m : Γ(L, U))
    (hm : meromorphicGenericValue X L s = L.presheaf.germ U (genericPoint X) hη m)
    (hmB : Hom.app e.hom ⊤ (pullbackSectionHom i L U ⊤ hB.ge m) = (1 : Γ(B, ⊤))) :
    ∃ (W : Stacks.Chow.DenseOpen X) (u : Γ(X, W.val)ˣ)
      (hBW : (⊤ : B.Opens) ≤ i ⁻¹ᵁ W.val),
      Units.map (Stacks.Chow.ofSectionRingHom X W).toMonoidHom u =
        tensorPowerCorrectionRatio X L (differenceSheaf D E) s hs k α
          (canonicalDifferenceMeromorphicSection D E)
          (isRegularMeromorphicSection_canonicalDifferenceMeromorphicSection D E) ∧
      i.appLE W.val ⊤ hBW u.val = (1 : Γ(B, ⊤)) := by
  obtain ⟨V, hηV, hBV, cV, hcV, hcB⟩ :=
    exists_canonicalDifference_regularRepresentative_boundary_one i D E hD hE
  exact exists_denseOpen_unit_framedPowerCorrection_of_regularRepresentative i L
    (differenceSheaf D E) k α e (differenceSheafBoundaryIso i D E hD hE) hcompat
    s hs U hη hB m hm hmB
    (canonicalDifferenceMeromorphicSection D E)
    (isRegularMeromorphicSection_canonicalDifferenceMeromorphicSection D E)
    V hηV hBV cV hcV hcB

end AlgebraicGeometry
