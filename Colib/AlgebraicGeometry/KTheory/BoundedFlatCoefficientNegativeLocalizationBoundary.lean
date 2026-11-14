/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientFineLocalizationBoundary
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientNegativeTelescopeNaturality

/-!
# Localization on the original Bass negative groups

The prescribed signed cone boundary is transported to the original Bass groups.
The three consecutive positions use the literal restriction and support forget
maps, including degree zero, without asserting surjectivity to the open.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The explicit integer reindexing between adjacent original negative degrees. -/
def negativeLocalizationDegreeIso (i : ℕ) :
    stableHomotopyFunctor (-(i : ℤ)) ≅
      stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ) + 1) :=
  eqToIso (by congr 1; omega)

/-- The fixed signed boundary on the original negative groups, including K₀ to degree −1. -/
def boundedAboveFlatCoefficientNegativeLocalizationConnecting (i : ℕ) (a : Under R) :
    (Bass.negativeKFunctor i).obj ((boundedAboveFlatCoefficientQuasiCompactRow P).obj a) ⟶
      (Bass.supportedNegativeKFunctor (i + 1)).obj
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a) := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  exact (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom.app a ≫
    (negativeLocalizationDegreeIso i).hom.app
      ((boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor f).obj a) ≫
    boundedAboveFlatCoefficientFineLocalizationConnecting f a (-((i + 1 : ℕ) : ℤ)) ≫
    (boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison f (i + 1)).inv.app a

/-- The boundary followed by the original supported comparison is its specified signed formula. -/
@[reassoc]
theorem boundedAboveFlatCoefficientNegativeLocalizationConnecting_comparison
    (i : ℕ) (a : Under R) :
    letI : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
    boundedAboveFlatCoefficientNegativeLocalizationConnecting f i a ≫
      (boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison f (i + 1)).hom.app a =
    (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom.app a ≫
      (negativeLocalizationDegreeIso i).hom.app
        ((boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor f).obj a) ≫
      boundedAboveFlatCoefficientFineLocalizationConnecting f a (-((i + 1 : ℕ) : ℤ)) := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  simp only [boundedAboveFlatCoefficientNegativeLocalizationConnecting, Category.assoc,
    Iso.inv_hom_id_app]
  exact congrArg (fun t =>
    (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom.app a ≫
      (negativeLocalizationDegreeIso i).hom.app
        ((boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor f).obj a) ≫ t)
    (Category.comp_id _)

/-- Exactness at the original open negative group, including the original open K₀ group. -/
theorem boundedAboveFlatCoefficientNegativeLocalizationConnecting_exact_open
    (i : ℕ) (a : Under R) :
    Function.Exact ((boundedAboveFlatCoefficientOriginalNegativeKRestriction f i).app a)
      (boundedAboveFlatCoefficientNegativeLocalizationConnecting f i a) := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  let eQ := (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison Q i).app a ≪≫
    (negativeLocalizationDegreeIso i).app
      ((boundedAboveFlatCoefficientAmbientBassTelescopeFunctor Q).obj a)
  let eP := (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison P i).app a ≪≫
    (negativeLocalizationDegreeIso i).app
      ((boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor f).obj a)
  let eS := (boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison f (i + 1)).app a
  have hr : (boundedAboveFlatCoefficientOriginalNegativeKRestriction f i).app a ≫ eP.hom =
      eQ.hom ≫ (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ) + 1)).map
        ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a) := by
    have h0 : (boundedAboveFlatCoefficientOriginalNegativeKRestriction f i).app a ≫
        (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom.app a =
      (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison Q i).hom.app a ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a) :=
      NatTrans.congr_app (boundedAboveFlatCoefficientAmbientBassNegativeMap_fullOpen f i) a
    have h1 := (negativeLocalizationDegreeIso i).hom.naturality
      ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ (negativeLocalizationDegreeIso i).hom.app
        ((boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor f).obj a)) h0).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun t =>
              (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison Q i).hom.app a ≫ t)
              h1).trans (Category.assoc _ _ _).symm)))
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    eQ.addCommGroupIsoToAddEquiv eP.addCommGroupIsoToAddEquiv eS.addCommGroupIsoToAddEquiv
    (H := boundedAboveFlatCoefficientFineLocalizationConnecting_exact_open f a
      (-((i + 1 : ℕ) : ℤ)))
  · ext x
    exact (ConcreteCategory.congr_hom hr x).symm
  · ext x
    exact (ConcreteCategory.congr_hom
      (boundedAboveFlatCoefficientNegativeLocalizationConnecting_comparison f i a) x).symm

/-- Exactness at the original supported negative group after the fixed boundary. -/
theorem boundedAboveFlatCoefficientNegativeLocalizationConnecting_exact_supported
    (i : ℕ) (a : Under R) :
    Function.Exact (boundedAboveFlatCoefficientNegativeLocalizationConnecting f i a)
      ((Bass.supportedNegativeKForgetNat (i + 1)).app
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a)) := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  let eP := (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison P i).app a ≪≫
    (negativeLocalizationDegreeIso i).app
      ((boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor f).obj a)
  let eS := (boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison f (i + 1)).app a
  let eQ := (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison Q (i + 1)).app a
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    eP.addCommGroupIsoToAddEquiv eS.addCommGroupIsoToAddEquiv eQ.addCommGroupIsoToAddEquiv
    (H := boundedAboveFlatCoefficientFineLocalizationConnecting_exact_supported f a
      (-((i + 1 : ℕ) : ℤ)))
  · ext x
    exact (ConcreteCategory.congr_hom
      (boundedAboveFlatCoefficientNegativeLocalizationConnecting_comparison f i a) x).symm
  · ext x
    exact (ConcreteCategory.congr_hom
      (boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison_forget_app
        f (i + 1) a) x).symm

/-- Original supported negative classes are precisely the kernel of original open pullback.
This includes the original supported K₀ image statement when `i = 0`.
-/
theorem boundedAboveFlatCoefficientSupportedNegativeK_localization_exact
    (i : ℕ) (a : Under R) :
    Function.Exact
      ((Bass.supportedNegativeKForgetNat i).app
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a))
      ((boundedAboveFlatCoefficientOriginalNegativeKRestriction f i).app a) := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  let H := stableHomotopyFunctor (-(i : ℤ))
  let eS := (boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison f i).app a
  let eQ := (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison Q i).app a
  let eP := (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison P i).app a
  let j := (Bass.supportedNegativeKForgetNat i).app
    ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a)
  let r := (boundedAboveFlatCoefficientOriginalNegativeKRestriction f i).app a
  let j' := H.map ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
  let r' := H.map ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
  have hj : j ≫ eQ.hom = eS.hom ≫ j' :=
    boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison_forget_app f i a
  have hr : r ≫ eP.hom = eQ.hom ≫ r' :=
    NatTrans.congr_app (boundedAboveFlatCoefficientAmbientBassNegativeMap_fullOpen f i) a
  have he : Function.Exact j' r' :=
    boundedAboveFlatCoefficientSupportedBassTelescope_fullOpen_exact f a (-(i : ℤ))
  change Function.Exact j r
  intro y
  constructor
  · intro hy
    have hy' : r' (eQ.hom y) = 0 := by
      calc
        _ = eP.hom (r y) := (ConcreteCategory.congr_hom hr y).symm
        _ = 0 := by rw [hy, map_zero]
    obtain ⟨z, hz⟩ := (he (eQ.hom y)).mp hy'
    obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso eS.hom).surjective z
    refine ⟨x, (ConcreteCategory.bijective_of_isIso eQ.hom).injective ?_⟩
    exact (ConcreteCategory.congr_hom hj x).trans hz
  · rintro ⟨x, rfl⟩
    apply (ConcreteCategory.bijective_of_isIso eP.hom).injective
    calc
      _ = r' (eQ.hom (j x)) := ConcreteCategory.congr_hom hr (j x)
      _ = r' (j' (eS.hom x)) :=
        congrArg r' (ConcreteCategory.congr_hom hj x)
      _ = 0 := he.apply_apply_eq_zero _
      _ = eP.hom 0 := (map_zero eP.hom.hom).symm

/-- At degree zero this is the original supported K₀ image, without open surjectivity. -/
theorem boundedAboveFlatCoefficientSupportedKZero_localization_exact (a : Under R) :
    Function.Exact
      (Bass.supportedKZeroForget.app
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a))
      (Bass.perfectKZeroFunctor.map
        ((boundedAboveFlatCoefficientQuasiCompactRowRestriction f).app a)) :=
  boundedAboveFlatCoefficientSupportedNegativeK_localization_exact f 0 a

end AlgebraicGeometry.Scheme.Modules
