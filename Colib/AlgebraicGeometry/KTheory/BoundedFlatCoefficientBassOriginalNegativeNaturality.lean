/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassOriginalNegativeComparison
public import
  Colib.AlgebraicGeometry.Scheme.CoefficientPolynomialLaurentSchemeNaturality
public import Colib.KTheory.Bass.DiagramTransportNaturality

/-!
Source directory: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/`.
Module: `CoefficientBassOriginalNegativeNaturality.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Scheme restriction for the original finite native negative-group comparison

For an arbitrary scheme-over-base arrow with compact source and target, the
existing comparison preserves the actual original group pullback and the
original finite strict Model restriction. All transformations retain every
coefficient arrow. No supported, transition, seed or telescope assertion occurs.
-/

@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS KTheory.Bass
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u w
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)

/-- Finite restriction is the iteration of the existing joint native Model map. -/
def boundedAboveFlatCoefficientAmbientBassSchemeRestriction (i : ℕ) :
    boundedAboveFlatCoefficientAmbientBassDiagram Q i ⟶
      boundedAboveFlatCoefficientAmbientBassDiagram P i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (Functor.whiskerRight (boundedAboveFlatCoefficientSectionModelRestriction f) prespectrumFunctor)

/-- The bottom action applies the original signed stable homotopy functor. -/
def boundedAboveFlatCoefficientAmbientBassBottomSchemeRestriction (i : ℕ) :
    boundedAboveFlatCoefficientAmbientBassDiagram Q i ⋙ stableHomotopyFunctor (-(i : ℤ)) ⟶
      boundedAboveFlatCoefficientAmbientBassDiagram P i ⋙ stableHomotopyFunctor (-(i : ℤ)) :=
  Functor.whiskerRight (boundedAboveFlatCoefficientAmbientBassSchemeRestriction f i)
    (stableHomotopyFunctor (-(i : ℤ)))

/-- Degree zero is literally the original uniterated Model restriction. -/
theorem boundedAboveFlatCoefficientAmbientBassBottomSchemeRestriction_zero (a : Under R) :
    (boundedAboveFlatCoefficientAmbientBassBottomSchemeRestriction f 0).app a =
      (stableHomotopyFunctor 0).map
        (prespectrumFunctor.map
          ((boundedAboveFlatCoefficientSectionModelRestriction f).app a)) := rfl

/-- The genuine signed bottom contraction preserves the original scheme restriction. -/
@[reassoc]
theorem boundedAboveFlatCoefficientAmbientBassBottomContractionIso_schemeRestriction
    (i : ℕ) (a : Under R) :
    (KTheory.Bass.TwoChart.contractionMap (underToLaurent R) (underToLaurentInvert R)
      (boundedAboveFlatCoefficientAmbientBassBottomSchemeRestriction f i)).app a ≫
        (boundedAboveFlatCoefficientAmbientBassBottomContractionIso P i).hom.app a =
    (boundedAboveFlatCoefficientAmbientBassBottomContractionIso Q i).hom.app a ≫
      (boundedAboveFlatCoefficientAmbientBassBottomSchemeRestriction f (i + 1)).app a :=
  modelDiagramBottomContractionIso_map
    (Functor.whiskerRight (boundedAboveFlatCoefficientSectionModelRestriction f)
      prespectrumFunctor) i a

variable [CompactSpace P.left] [CompactSpace Q.left]

/-- The original native scheme pullback, lifted to the actual quasi-compact opposite rows. -/
def boundedAboveFlatCoefficientQuasiCompactRowRestriction :
    boundedAboveFlatCoefficientQuasiCompactRow Q ⟶
      boundedAboveFlatCoefficientQuasiCompactRow P where
  app a := (AlgebraicGeometry.Scheme.quasiCompactScheme.homMk (schemeMap f a)).op
  naturality {a b} g := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact schemeMap_coefficientMap f g

/-- Every original group restriction is the already defined Bass functor on that scheme map. -/
def boundedAboveFlatCoefficientOriginalNegativeKRestriction (i : ℕ) :
    boundedAboveFlatCoefficientQuasiCompactRow Q ⋙ Bass.negativeKFunctor i ⟶
      boundedAboveFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor i :=
  Functor.whiskerRight (boundedAboveFlatCoefficientQuasiCompactRowRestriction f)
    (Bass.negativeKFunctor i)

/-- The true Laurent product identification retains the same original scheme pullback. -/
@[reassoc]
theorem boundedAboveFlatCoefficientLaurentIso_schemeRestriction (a : Under R) :
    (boundedAboveFlatCoefficientQuasiCompactRowRestriction f).app
        ((laurentUnderFunctor R).obj a) ≫
      (boundedAboveFlatCoefficientLaurentIso P).hom.app a =
    (boundedAboveFlatCoefficientLaurentIso Q).hom.app a ≫
      AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.op.map
        ((boundedAboveFlatCoefficientQuasiCompactRowRestriction f).app a) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  change (laurentIso P a).inv ≫
      schemeMap f ((laurentUnderFunctor R).obj a) =
    (AlgebraicGeometry.Scheme.Products.baseProductFunctor
      (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
        (CommRingCat.of (ULift.{u} ℤ)))).map
        (schemeMap f a) ≫ (laurentIso Q a).inv
  apply (cancel_mono (laurentIso Q a).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [laurentIso_schemeMap f a, Iso.inv_hom_id_assoc]

/-- Original chart transport retains the actual restriction between compact native schemes. -/
@[reassoc]
theorem boundedAboveFlatCoefficientContractionTransportIso_schemeRestriction
    (F : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) (a : Under R) :
    (KTheory.Bass.TwoChart.contractionMap (underToLaurent R) (underToLaurentInvert R)
      (Functor.whiskerRight (boundedAboveFlatCoefficientQuasiCompactRowRestriction f) F)).app a ≫
        (boundedAboveFlatCoefficientContractionTransportIso P F).hom.app a =
    (boundedAboveFlatCoefficientContractionTransportIso Q F).hom.app a ≫
      (KTheory.Bass.TwoChart.contraction (NatTrans.op
        AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus)
        (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus) F).map
          ((boundedAboveFlatCoefficientQuasiCompactRowRestriction f).app a) :=
  KTheory.Bass.TwoChart.contractionTransportIso_map
    (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus) (NatTrans.op
      AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus)
    (underToLaurent R) (underToLaurentInvert R)
    (boundedAboveFlatCoefficientQuasiCompactRow Q) (boundedAboveFlatCoefficientQuasiCompactRow P)
    (boundedAboveFlatCoefficientPolynomialIso Q) (boundedAboveFlatCoefficientLaurentIso Q)
    (boundedAboveFlatCoefficientPolynomialIso P) (boundedAboveFlatCoefficientLaurentIso P)
    (boundedAboveFlatCoefficientPolynomialLaurentIso_plus Q)
    (boundedAboveFlatCoefficientPolynomialLaurentIso_minus Q)
    (boundedAboveFlatCoefficientPolynomialLaurentIso_plus P)
    (boundedAboveFlatCoefficientPolynomialLaurentIso_minus P)
    (boundedAboveFlatCoefficientQuasiCompactRowRestriction f)
    (boundedAboveFlatCoefficientLaurentIso_schemeRestriction f) F a

/-- The inverse transport retains exactly the same original scheme restriction. -/
@[reassoc]
theorem boundedAboveFlatCoefficientContractionTransportIso_schemeRestriction_inv
    (F : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) (a : Under R) :
    (KTheory.Bass.TwoChart.contraction (NatTrans.op
      AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus)
      (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus) F).map
        ((boundedAboveFlatCoefficientQuasiCompactRowRestriction f).app a) ≫
      (boundedAboveFlatCoefficientContractionTransportIso P F).inv.app a =
    (boundedAboveFlatCoefficientContractionTransportIso Q F).inv.app a ≫
      (KTheory.Bass.TwoChart.contractionMap (underToLaurent R) (underToLaurentInvert R)
        (Functor.whiskerRight
          (boundedAboveFlatCoefficientQuasiCompactRowRestriction f) F)).app a := by
  apply (cancel_mono ((boundedAboveFlatCoefficientContractionTransportIso P F).hom.app a)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [boundedAboveFlatCoefficientContractionTransportIso_schemeRestriction,
    Iso.inv_hom_id_app_assoc]
  exact Category.comp_id _

/-- Joint normalized evaluation followed by the original inclusion preserves every scheme arrow. -/
@[reassoc]
theorem boundedAboveFlatCoefficientSectionPerfectEvaluation_schemeRestriction (a : Under R) :
    toStableLocalization.map
        ((Functor.whiskerRight (boundedAboveFlatCoefficientSectionModelRestriction f)
          prespectrumFunctor).app a) ≫
      (boundedAboveFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso P).hom.app a =
    (boundedAboveFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso Q).hom.app a ≫
      perfectLocalizedSpectrumFunctor.map
        ((boundedAboveFlatCoefficientQuasiCompactRowRestriction f).app a) := by
  have hE := (boundedAboveFlatCoefficientSectionEvaluationLocalizedNatIso R).hom.naturality
    (show (op Q, a) ⟶ (op P, a) from (f.op, 𝟙 a))
  have hI := boundedAboveFlatPerfectSpectrumNatIso.hom.naturality
    ((boundedAboveFlatCoefficientQuasiCompactRowRestriction f).app a)
  change (boundedAboveFlatCoefficientSectionLocalizedSpectrumFunctor R).map (f.op, 𝟙 a) ≫
      (boundedAboveFlatCoefficientSectionEvaluationLocalizedNatIso R).hom.app (op P, a) =
    (boundedAboveFlatCoefficientSectionEvaluationLocalizedNatIso R).hom.app (op Q, a) ≫
      boundedAboveFlatLocalizedPullback (schemeMap f a) at hE
  change boundedAboveFlatLocalizedPullback (schemeMap f a) ≫
      boundedAboveFlatPerfectSpectrumNatIso.hom.app
        ((boundedAboveFlatCoefficientQuasiCompactRow P).obj a) =
    boundedAboveFlatPerfectSpectrumNatIso.hom.app
        ((boundedAboveFlatCoefficientQuasiCompactRow Q).obj a) ≫
      perfectLocalizedSpectrumFunctor.map
        ((boundedAboveFlatCoefficientQuasiCompactRowRestriction f).app a) at hI
  change (boundedAboveFlatCoefficientSectionLocalizedSpectrumFunctor R).map (f.op, 𝟙 a) ≫
      ((boundedAboveFlatCoefficientSectionEvaluationLocalizedNatIso R).hom.app (op P, a) ≫
        boundedAboveFlatPerfectSpectrumNatIso.hom.app
          ((boundedAboveFlatCoefficientQuasiCompactRow P).obj a)) =
    ((boundedAboveFlatCoefficientSectionEvaluationLocalizedNatIso R).hom.app (op Q, a) ≫
      boundedAboveFlatPerfectSpectrumNatIso.hom.app
        ((boundedAboveFlatCoefficientQuasiCompactRow Q).obj a)) ≫ _
  rw [← Category.assoc, hE, Category.assoc, hI, ← Category.assoc]

/-- Original perfect K-zero and the actual degree-zero Model restriction commute. -/
@[reassoc]
theorem boundedAboveFlatCoefficientAmbientBassBottomZeroNatIso_schemeRestriction (a : Under R) :
    (boundedAboveFlatCoefficientOriginalNegativeKRestriction f 0).app a ≫
      (boundedAboveFlatCoefficientAmbientBassBottomZeroNatIso P).hom.app a =
    (boundedAboveFlatCoefficientAmbientBassBottomZeroNatIso Q).hom.app a ≫
      (boundedAboveFlatCoefficientAmbientBassBottomSchemeRestriction f 0).app a := by
  let Eₚ := Functor.isoWhiskerRight
    (boundedAboveFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso P)
    (localizedStableHomotopyFunctor 0)
  let Eᵩ := Functor.isoWhiskerRight
    (boundedAboveFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso Q)
    (localizedStableHomotopyFunctor 0)
  have hE : (boundedAboveFlatCoefficientAmbientBassBottomSchemeRestriction f 0).app a ≫
      Eₚ.hom.app a = Eᵩ.hom.app a ≫
        (perfectLocalizedSpectrumFunctor ⋙ localizedStableHomotopyFunctor 0).map
          ((boundedAboveFlatCoefficientQuasiCompactRowRestriction f).app a) := by
    have h := congrArg ((localizedStableHomotopyFunctor 0).map)
      (boundedAboveFlatCoefficientSectionPerfectEvaluation_schemeRestriction f a)
    simpa only [Functor.map_comp, localizedStableHomotopyFunctor_original_map,
      Functor.comp_map, Eₚ, Eᵩ, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      boundedAboveFlatCoefficientAmbientBassBottomSchemeRestriction_zero]
      using h
  apply (cancel_mono (Eₚ.hom.app a)).mp
  change ((_ ≫ (perfectKZeroLocalizedStableIso
      ((boundedAboveFlatCoefficientQuasiCompactRow P).obj a)).hom ≫ Eₚ.inv.app a) ≫
      Eₚ.hom.app a) =
    (((perfectKZeroLocalizedStableIso
      ((boundedAboveFlatCoefficientQuasiCompactRow Q).obj a)).hom ≫ Eᵩ.inv.app a) ≫ _) ≫
      Eₚ.hom.app a
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [hE, Iso.inv_hom_id_app_assoc]
  exact perfectKZeroLocalizedStableIso_naturality
    ((boundedAboveFlatCoefficientQuasiCompactRowRestriction f).app a)

/-- The existing assembled comparison retains original restriction in every finite degree. -/
theorem boundedAboveFlatCoefficientAmbientNegativeKComparison_schemeRestriction (i : ℕ) :
    boundedAboveFlatCoefficientOriginalNegativeKRestriction f i ≫
      (boundedAboveFlatCoefficientAmbientNegativeKComparison P i).hom =
    (boundedAboveFlatCoefficientAmbientNegativeKComparison Q i).hom ≫
      boundedAboveFlatCoefficientAmbientBassBottomSchemeRestriction f i := by
  induction i with
  | zero =>
      apply NatTrans.ext
      funext a
      exact boundedAboveFlatCoefficientAmbientBassBottomZeroNatIso_schemeRestriction f a
  | succ i ih =>
      apply NatTrans.ext
      funext a
      let τₚ := boundedAboveFlatCoefficientContractionTransportIso P (Bass.negativeKFunctor i)
      let τᵩ := boundedAboveFlatCoefficientContractionTransportIso Q (Bass.negativeKFunctor i)
      let γₚ := boundedAboveFlatCoefficientAmbientNegativeKComparison P i
      let γᵩ := boundedAboveFlatCoefficientAmbientNegativeKComparison Q i
      let βₚ := boundedAboveFlatCoefficientAmbientBassBottomContractionIso P i
      let βᵩ := boundedAboveFlatCoefficientAmbientBassBottomContractionIso Q i
      let C := KTheory.Bass.TwoChart.contractionFunctor
        (underToLaurent R) (underToLaurentInvert R)
      let r := (boundedAboveFlatCoefficientOriginalNegativeKRestriction f (i + 1)).app a
      let k := (C.map (boundedAboveFlatCoefficientOriginalNegativeKRestriction f i)).app a
      let gₚ := (C.map γₚ.hom).app a
      let gᵩ := (C.map γᵩ.hom).app a
      let s := (C.map (boundedAboveFlatCoefficientAmbientBassBottomSchemeRestriction f i)).app a
      let t := (boundedAboveFlatCoefficientAmbientBassBottomSchemeRestriction f (i + 1)).app a
      have hT : r ≫ τₚ.inv.app a = τᵩ.inv.app a ≫ k :=
        boundedAboveFlatCoefficientContractionTransportIso_schemeRestriction_inv f
          (Bass.negativeKFunctor i) a
      have hC : k ≫ gₚ = gᵩ ≫ s := by
        have h := congrArg (fun η ↦ (C.map η).app a) ih
        simpa only [Functor.map_comp, NatTrans.comp_app] using h
      have hB : s ≫ βₚ.hom.app a = βᵩ.hom.app a ≫ t :=
        boundedAboveFlatCoefficientAmbientBassBottomContractionIso_schemeRestriction f i a
      change r ≫ (τₚ.inv.app a ≫ gₚ ≫ βₚ.hom.app a) =
        (τᵩ.inv.app a ≫ gᵩ ≫ βᵩ.hom.app a) ≫ t
      calc
        r ≫ (τₚ.inv.app a ≫ gₚ ≫ βₚ.hom.app a) =
            (r ≫ τₚ.inv.app a) ≫ gₚ ≫ βₚ.hom.app a := by simp only [Category.assoc]
        _ = (τᵩ.inv.app a ≫ k) ≫ gₚ ≫ βₚ.hom.app a := by rw [hT]
        _ = τᵩ.inv.app a ≫ (k ≫ gₚ) ≫ βₚ.hom.app a := by simp only [Category.assoc]
        _ = τᵩ.inv.app a ≫ (gᵩ ≫ s) ≫ βₚ.hom.app a := by rw [hC]
        _ = τᵩ.inv.app a ≫ gᵩ ≫ (s ≫ βₚ.hom.app a) := by simp only [Category.assoc]
        _ = τᵩ.inv.app a ≫ gᵩ ≫ (βᵩ.hom.app a ≫ t) := by rw [hB]
        _ = (τᵩ.inv.app a ≫ gᵩ ≫ βᵩ.hom.app a) ≫ t := by simp only [Category.assoc]

/-- Component form keeps the original scheme pullback and actual finite spectral map explicit. -/
@[reassoc]
theorem boundedAboveFlatCoefficientAmbientNegativeKComparison_schemeRestriction_app
    (i : ℕ) (a : Under R) :
    (Bass.negativeKFunctor i).map
        (AlgebraicGeometry.Scheme.quasiCompactScheme.homMk (schemeMap f a)).op ≫
      (boundedAboveFlatCoefficientAmbientNegativeKComparison P i).hom.app a =
    (boundedAboveFlatCoefficientAmbientNegativeKComparison Q i).hom.app a ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        (((strictDiagramIterate (laurentUnderSquareFunctor R) i).map
          (Functor.whiskerRight (boundedAboveFlatCoefficientSectionModelRestriction f)
            prespectrumFunctor)).app a) :=
  congrArg (fun η ↦ η.app a)
    (boundedAboveFlatCoefficientAmbientNegativeKComparison_schemeRestriction f i)

end AlgebraicGeometry.Scheme.Modules
