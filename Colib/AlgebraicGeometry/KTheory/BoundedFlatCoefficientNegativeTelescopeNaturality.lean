/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedNegativeForgetComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFineTelescopeComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAmbientFineTelescopeComparison

/-!
# Original negative support forgetting in the actual fine telescopes

The existing supported and ambient negative-group comparisons commute with the original
forget-support telescope map. The proof retains the finite-bottom square and the literal
stage-inclusion square. Original Laurent quotients and actual telescope inclusions are
unchanged. The ambient scheme is qcqs and the removed open is compact.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The original negative support-forgetting map agrees with the actual fine-telescope map. -/
@[reassoc]
theorem boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison_forget_app
    (i : ℕ) (a : Under R) :
    (Bass.supportedNegativeKForgetNat i).app
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a) ≫
      (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison Q i).hom.app a =
    (boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison f i).hom.app a ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a) := by
  rw [boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison_hom_app,
    boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison_hom_app,
    ← Category.assoc, boundedAboveFlatCoefficientSupportedNegativeKComparison_forget_app]
  simp only [Category.assoc, ← Functor.map_comp]
  exact congrArg (fun h ↦
    (boundedAboveFlatCoefficientSupportedNegativeKComparison f i).hom.app a ≫
    (stableHomotopyFunctor (-(i : ℤ))).map h)
    (NatTrans.congr_app
      (boundedAboveFlatCoefficientSupportedBassTelescopeInclusion_forget f i) a).symm

/-- The same actual forget-support square is natural on the full coefficient category. -/
theorem boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison_forget (i : ℕ) :
    Functor.whiskerLeft (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f)
        (Bass.supportedNegativeKForgetNat i) ≫
      (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison Q i).hom =
    (boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison f i).hom ≫
      Functor.whiskerRight (boundedAboveFlatCoefficientSupportedBassTelescopeForget f)
        (stableHomotopyFunctor (-(i : ℤ))) := by
  apply NatTrans.ext
  funext a
  exact boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison_forget_app f i a

/-- The unchanged Laurent quotient keeps its actual supported stage inclusion after forgetting. -/
@[reassoc]
theorem boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison_π_forget
    (i : ℕ) (a : Under R) :
    (Bass.supportedNegativeKFunctor i).map
        ((boundedAboveFlatCoefficientSupportedLaurentIso f).hom.app a) ≫
      Bass.supportedNegativeKπ
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a).unop i ≫
      (Bass.supportedNegativeKForgetNat (i + 1)).app
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a) ≫
      (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison Q (i + 1)).hom.app a =
    (boundedAboveFlatCoefficientSupportedNegativeKComparison f i).hom.app
        ((laurentUnderFunctor R).obj a) ≫
      (KTheory.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
        (boundedAboveFlatCoefficientSupportedBassDiagram f i ⋙
          stableHomotopyFunctor (-(i : ℤ)))).app a ≫
      (boundedAboveFlatCoefficientSupportedBassBottomContractionIso f i).hom.app a ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedAboveFlatCoefficientSupportedBassTelescopeInclusion f (i + 1)).app a) ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a) := by
  rw [boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison_forget_app]
  exact boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison_π_assoc f i a _

end AlgebraicGeometry.Scheme.Modules
