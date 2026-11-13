/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicGeometry.KTheory.Bass.SupportedGroups
public import Colib.AlgebraicGeometry.KTheory.Bass.NegativeGroups
public import Colib.KTheory.Bass.DiagramTransport

/-!
Source: `Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedForget.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

The original forget-support K0 map extends naturally through every actual Bass cokernel. All-degree
pair naturality and the literal Laurent representative square are preserved by the genuine geometric
chart identification.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules

local instance (A : QuasiCompactOpenPairs.{u}) : CompactSpace A.obj.right := A.property

/-- The unchanged all-perfect support-forgetting map commutes with actual pair pullback. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/PairPullback.lean:155-172"
  "adaptation" "Original support-forgetting square through literal flat inclusions."]
theorem perfectSupportedKMap_pullback {A B : QuasiCompactOpenPairs.{u}}
    (f : A ⟶ B) (n : ℕ) :
    (perfectKPullback f.hom.right n).comp (perfectSupportedKMap B.obj.hom n) =
      (perfectSupportedKMap A.obj.hom n).comp (perfectSupportedKPullback f n) := by
  ext x
  obtain ⟨y, rfl⟩ := (boundedAboveFlatPerfectSupportedToPerfectKMap_bijective B.obj.hom
    n).surjective x
  have h₁ := DFunLike.congr_fun
    (boundedAboveFlatPerfectSupportedToPerfectKMap_forget B.obj.hom n) y
  have h₂ := DFunLike.congr_fun (perfectSupportedKPullback_comp_boundedFlat f n) y
  simp only [MonoidHom.comp_apply] at h₁ h₂ ⊢
  have h₃ := DFunLike.congr_fun (boundedAboveFlatPerfectToPerfectKMap_pullback f.hom.right n)
    (boundedAboveFlatPerfectSupportedForgetKMap B.obj.hom n y)
  have h₄ := DFunLike.congr_fun
    (boundedAboveFlatPerfectSupportedToPerfectKMap_forget A.obj.hom n)
    (boundedAboveFlatPerfectSupportedKPullback f.hom n y)
  have h₅ := DFunLike.congr_fun
    (boundedAboveFlatPerfectSupportedForgetKMap_pullback f.hom n) y
  simp only [MonoidHom.comp_apply] at h₃ h₄ h₅
  exact (congrArg (perfectKPullback f.hom.right n) h₁).trans
    (h₃.trans ((congrArg
      (boundedAboveFlatPerfectToPerfectKMap A.obj.right.toRingedSpace n) h₅).trans
        (h₄.symm.trans (congrArg (perfectSupportedKMap A.obj.hom n) h₂.symm))))

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Bass
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules

/-- The original supported-to-absolute K0 homomorphism as a genuine natural transformation. -/
def supportedKZeroForget : supportedKZeroFunctor.{u} ⟶
    quasiCompactOpenPairsBase.op ⋙ perfectKZeroFunctor where
  app A := AddCommGrpCat.ofHom (perfectSupportedKMap A.unop.obj.hom 0).toAdditive
  naturality {A B} f := by
    apply AddCommGrpCat.hom_ext
    exact congrArg MonoidHom.toAdditive (perfectSupportedKMap_pullback f.unop 0).symm

/-- Forgetting the open retains the exact polynomial/Laurent quotient diagram. -/
def supportedContractionForgetIso
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    KTheory.Bass.TwoChart.contraction (NatTrans.op Scheme.Bass.pairPlus)
      (NatTrans.op Scheme.Bass.pairMinus) (quasiCompactOpenPairsBase.op ⋙ F) ≅
    quasiCompactOpenPairsBase.op ⋙
      KTheory.Bass.TwoChart.contraction (NatTrans.op
        AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus) (NatTrans.op
        AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus) F :=
  KTheory.Bass.TwoChart.contractionTransportIso (NatTrans.op
    AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus) (NatTrans.op
    AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus)
    (NatTrans.op Scheme.Bass.pairPlus) (NatTrans.op Scheme.Bass.pairMinus)
    quasiCompactOpenPairsBase.op (Iso.refl _) (Iso.refl _)
    (by intro A; rfl)
    (by intro A; rfl) F

/-- The actual original forget-support map extends through every Bass cokernel. -/
def supportedNegativeKForgetNat : (n : ℕ) → supportedNegativeKFunctor.{u} n ⟶
    quasiCompactOpenPairsBase.op ⋙ negativeKFunctor n
  | 0 => supportedKZeroForget
  | n+1 => KTheory.Bass.TwoChart.contractionMap (NatTrans.op Scheme.Bass.pairPlus)
      (NatTrans.op Scheme.Bass.pairMinus) (supportedNegativeKForgetNat n) ≫
        (supportedContractionForgetIso (negativeKFunctor n)).hom

/-- The component of the forget-support map on the actual iterated Bass groups. -/
abbrev supportedNegativeKForget (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    supportedNegativeK A n ⟶ negativeK (quasiCompactOpenPairsBase.obj A) n :=
  (supportedNegativeKForgetNat n).app (op A)

@[simp] lemma supportedNegativeKForget_zero (A : QuasiCompactOpenPairs.{u})
    (a : PerfectSupportedK A.obj.hom 0) :
    supportedNegativeKForget A 0 (Additive.ofMul a) =
      Additive.ofMul (perfectSupportedKMap A.obj.hom 0 a) := rfl

/-- Arbitrary pair pullback commutes with the actual forget-support map in every degree. -/
@[reassoc] lemma supportedNegativeKForget_naturality {A B : QuasiCompactOpenPairs.{u}}
    (f : A ⟶ B) (n : ℕ) :
    supportedNegativeKPullback f n ≫ supportedNegativeKForget A n =
      supportedNegativeKForget B n ≫ negativeKPullback (quasiCompactOpenPairsBase.map f) n :=
  (supportedNegativeKForgetNat n).naturality f.op

/-- The original supported Laurent representative square is retained, without a model change. -/
@[reassoc] lemma supportedNegativeKForget_π (A : QuasiCompactOpenPairs.{u}) (n : ℕ) :
    supportedNegativeKπ A n ≫ supportedNegativeKForget A (n+1) =
      supportedNegativeKForget (Scheme.Bass.pairLaurentFunctor.obj A) n ≫
        negativeKπ (quasiCompactOpenPairsBase.obj A) n := by
  change (KTheory.Bass.TwoChart.contractionπ _ _ (supportedNegativeKFunctor n)).app (op A) ≫
    (KTheory.Bass.TwoChart.contractionMap _ _ (supportedNegativeKForgetNat n)).app (op A) ≫
      (supportedContractionForgetIso (negativeKFunctor n)).hom.app (op A) = _
  rw [KTheory.Bass.TwoChart.contractionMap_π_assoc]
  unfold supportedContractionForgetIso
  rw [KTheory.Bass.TwoChart.contractionTransportIso_π]
  change supportedNegativeKForget (Scheme.Bass.pairLaurentFunctor.obj A) n ≫
    (negativeKFunctor n).map (𝟙 _) ≫ negativeKπ (quasiCompactOpenPairsBase.obj A) n = _
  rw [(negativeKFunctor n).map_id,Category.id_comp]

end AlgebraicGeometry.Scheme.Bass

end

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedForget.lean:30"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedKZeroForget

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedForget.lean:38"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedContractionForgetIso

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedForget.lean:55"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeKForgetNat

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedForget.lean:63"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeKForget

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedForget.lean:67"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeKForget_zero

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedForget.lean:73"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeKForget_naturality

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Bass/SupportedForget.lean:80"
  "adaptation" "Original supported Bass quotient and its unchanged maps."]
  AlgebraicGeometry.Scheme.Bass.supportedNegativeKForget_π
