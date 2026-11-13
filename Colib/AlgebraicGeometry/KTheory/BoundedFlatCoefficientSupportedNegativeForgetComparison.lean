/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedKZeroForgetComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedContractionForget
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedNegativeBottomComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassOriginalNegativeComparison

/-!
Source in `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/`:
`CoefficientSupportedNegativeForgetComparison.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Original negative support forgetting at every actual finite bottom

The unchanged supported and ambient negative-group comparisons commute with the original
forget-support map. The induction uses actual coefficient contraction transport, its
original group-map naturality and the existing finite-stage forget square. It does not
choose replacement comparisons or assume injectivity of any support-forgetting map.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum
open CommRingCat.PolynomialLaurent KTheory.Bass.TwoChart
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- Every original negative support-forgetting map is the existing finite-bottom map. -/
theorem boundedAboveFlatCoefficientSupportedNegativeKComparison_forget (i : ℕ) :
    Functor.whiskerLeft (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f)
        (Bass.supportedNegativeKForgetNat i) ≫
      (boundedAboveFlatCoefficientAmbientNegativeKComparison Q i).hom =
    (boundedAboveFlatCoefficientSupportedNegativeKComparison f i).hom ≫
      Functor.whiskerRight (boundedAboveFlatCoefficientSupportedBassForget f i)
        (stableHomotopyFunctor (-(i : ℤ))) := by
  induction i with
  | zero =>
      apply NatTrans.ext
      funext a
      exact boundedAboveFlatCoefficientSupportedBassBottomZeroIso_forget f a
  | succ i ih =>
      let B := contractionFunctor (underToLaurent R) (underToLaurentInvert R)
      let α := Functor.whiskerLeft (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f)
        (Bass.supportedNegativeKForgetNat i)
      let α' := Functor.whiskerLeft (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f)
        (Bass.supportedNegativeKForgetNat (i + 1))
      let β := Functor.whiskerRight (boundedAboveFlatCoefficientSupportedBassForget f i)
        (stableHomotopyFunctor (-(i : ℤ)))
      let β' := Functor.whiskerRight (boundedAboveFlatCoefficientSupportedBassForget f (i + 1))
        (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ)))
      let γS := boundedAboveFlatCoefficientSupportedNegativeKComparison f i
      let γA := boundedAboveFlatCoefficientAmbientNegativeKComparison Q i
      let τS := boundedAboveFlatCoefficientSupportedContractionTransportIso f
        (Bass.supportedNegativeKFunctor i)
      let τA := boundedAboveFlatCoefficientContractionTransportIso Q (Bass.negativeKFunctor i)
      let bS := boundedAboveFlatCoefficientSupportedBassBottomContractionIso f i
      let bA := boundedAboveFlatCoefficientAmbientBassBottomContractionIso Q i
      have hτ : τS.hom ≫ α' = B.map α ≫ τA.hom :=
        boundedAboveFlatCoefficientSupportedContractionTransportIso_negativeForget f i
      have hβ : B.map β ≫ bA.hom = bS.hom ≫ β' := by
        apply NatTrans.ext
        funext a
        exact boundedAboveFlatCoefficientSupportedBassBottomContractionIso_forget f i a
      have hi : α ≫ γA.hom = γS.hom ≫ β := ih
      apply (cancel_epi τS.hom).mp
      change τS.hom ≫ (α' ≫ (τA.inv ≫ B.map γA.hom ≫ bA.hom)) =
        τS.hom ≫ ((τS.inv ≫ B.map γS.hom ≫ bS.hom) ≫ β')
      rw [← Category.assoc τS.hom α', hτ]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Category.assoc, ← B.map_comp, hi, B.map_comp]
      simp only [Category.assoc]
      rw [hβ]

/-- The component square retains the actual original finite-stage spectrum inclusion. -/
@[reassoc]
theorem boundedAboveFlatCoefficientSupportedNegativeKComparison_forget_app (i : ℕ) (a : Under R) :
    (Bass.supportedNegativeKForgetNat i).app
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a) ≫
      (boundedAboveFlatCoefficientAmbientNegativeKComparison Q i).hom.app a =
    (boundedAboveFlatCoefficientSupportedNegativeKComparison f i).hom.app a ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        ((boundedAboveFlatCoefficientSupportedBassForget f i).app a) :=
  NatTrans.congr_app (boundedAboveFlatCoefficientSupportedNegativeKComparison_forget f i) a

/-- Original supported Laurent representatives keep their cone inclusion after forgetting support.
-/
@[reassoc]
theorem boundedAboveFlatCoefficientSupportedNegativeKComparison_π_cone_forget
    (i : ℕ) (a : Under R) :
    (Bass.supportedNegativeKFunctor i).map
        ((boundedAboveFlatCoefficientSupportedLaurentIso f).hom.app a) ≫
      Bass.supportedNegativeKπ ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj
        a).unop i ≫
      (Bass.supportedNegativeKForgetNat (i + 1)).app
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a) ≫
      (boundedAboveFlatCoefficientAmbientNegativeKComparison Q (i + 1)).hom.app a =
    (boundedAboveFlatCoefficientSupportedNegativeKComparison f i).hom.app
        ((laurentUnderFunctor R).obj a) ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        (mappingConeInclusion (StrictSquare.comparison
          ((boundedAboveFlatCoefficientSupportedBassDiagram f i).mapArrow.mapArrow.obj
            (laurentUnderSquare R a)))) ≫
      (KTheory.Bass.modelDiagramBottomSuccessorIso
        (boundedAboveFlatCoefficientSupportedModelFunctor f) i).inv.app a ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedAboveFlatCoefficientSupportedBassForget f (i + 1)).app a) := by
  rw [boundedAboveFlatCoefficientSupportedNegativeKComparison_forget_app]
  exact boundedAboveFlatCoefficientSupportedNegativeKComparison_π_cone_assoc f i a _


attribute [colib_ref "quillen" "CoefficientSupportedNegativeForgetComparison.lean:33"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedNegativeKComparison_forget
attribute [colib_ref "quillen" "CoefficientSupportedNegativeForgetComparison.lean:80"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedNegativeKComparison_forget_app
attribute [colib_ref "quillen" "CoefficientSupportedNegativeForgetComparison.lean:92"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedNegativeKComparison_π_cone_forget

end AlgebraicGeometry.Scheme.Modules
