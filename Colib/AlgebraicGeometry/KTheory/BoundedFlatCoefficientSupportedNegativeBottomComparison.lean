/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedKZeroComparison
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedPolynomialLaurentTransport
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassBottomComparison

/-!
Source in `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/`:
`CoefficientSupportedNegativeBottomComparison.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Original supported negative K-groups at actual finite native bottoms

The original supported Bass recursion on scheme/open pairs is naturally the
bottom stable group of each finite supported Model stage. The comparison uses
the original supported K-zero evaluation and the genuine pair polynomial/Laurent
isomorphisms. Its representative equation retains the original supported quotient
and the actual finite-stage cone inclusion and signed shift. Compactness of the
ambient scheme suffices for this finite comparison. No invertibility of supported
transitions or comparison with their telescope is asserted.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- The original supported groups are naturally the bottom groups of every native finite stage. -/
def boundedAboveFlatCoefficientSupportedNegativeKComparison :
    (i : ℕ) → boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙
      Bass.supportedNegativeKFunctor i ≅
      boundedAboveFlatCoefficientSupportedBassDiagram f i ⋙ stableHomotopyFunctor (-(i : ℤ))
  | 0 => boundedAboveFlatCoefficientSupportedBassBottomZeroNatIso f
  | i + 1 => (boundedAboveFlatCoefficientSupportedContractionTransportIso f
      (Bass.supportedNegativeKFunctor i)).symm ≪≫
      (KTheory.Bass.TwoChart.contractionFunctor (underToLaurent R) (underToLaurentInvert R)).mapIso
        (boundedAboveFlatCoefficientSupportedNegativeKComparison i) ≪≫
      boundedAboveFlatCoefficientSupportedBassBottomContractionIso f i

/-- Every original supported Laurent representative is preserved by genuine product transport. -/
@[reassoc]
theorem boundedAboveFlatCoefficientSupportedNegativeKComparison_π (i : ℕ) (a : Under R) :
    (Bass.supportedNegativeKFunctor i).map
      ((boundedAboveFlatCoefficientSupportedLaurentIso f).hom.app a) ≫
      Bass.supportedNegativeKπ ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj
        a).unop i ≫
        (boundedAboveFlatCoefficientSupportedNegativeKComparison f (i + 1)).hom.app a =
    (boundedAboveFlatCoefficientSupportedNegativeKComparison f i).hom.app
        ((laurentUnderFunctor R).obj a) ≫
      (KTheory.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
        (boundedAboveFlatCoefficientSupportedBassDiagram f i ⋙
          stableHomotopyFunctor (-(i : ℤ)))).app a ≫
        (boundedAboveFlatCoefficientSupportedBassBottomContractionIso f i).hom.app a := by
  let τ := boundedAboveFlatCoefficientSupportedContractionTransportIso f
    (Bass.supportedNegativeKFunctor i)
  let γ := boundedAboveFlatCoefficientSupportedNegativeKComparison f i
  let β := boundedAboveFlatCoefficientSupportedBassBottomContractionIso f i
  have ht : (KTheory.Bass.TwoChart.contractionπ (underToLaurent R)
      (underToLaurentInvert R)
      (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedNegativeKFunctor
        i)).app a ≫
      τ.hom.app a =
    (Bass.supportedNegativeKFunctor i).map
      ((boundedAboveFlatCoefficientSupportedLaurentIso f).hom.app a) ≫
      Bass.supportedNegativeKπ ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj
        a).unop i :=
    boundedAboveFlatCoefficientSupportedContractionTransportIso_π f
      (Bass.supportedNegativeKFunctor i) a
  change _ ≫ _ ≫ (τ.inv.app a ≫
    (KTheory.Bass.TwoChart.contractionMap (underToLaurent R)
      (underToLaurentInvert R) γ.hom).app a ≫ β.hom.app a) = _
  have hcancel : τ.hom.app a ≫ τ.inv.app a ≫
      (KTheory.Bass.TwoChart.contractionMap (underToLaurent R)
        (underToLaurentInvert R) γ.hom).app a ≫ β.hom.app a =
    (KTheory.Bass.TwoChart.contractionMap (underToLaurent R)
      (underToLaurentInvert R) γ.hom).app a ≫ β.hom.app a :=
    (τ.app a).hom_inv_id_assoc _
  rw [← Category.assoc, ← ht, Category.assoc, hcancel]
  exact KTheory.Bass.TwoChart.contractionMap_π_assoc (underToLaurent R)
    (underToLaurentInvert R) γ.hom a (β.hom.app a)

/-- The same original quotient formula includes the actual cone inclusion and signed shift. -/
@[reassoc]
theorem boundedAboveFlatCoefficientSupportedNegativeKComparison_π_cone (i : ℕ) (a : Under R) :
    (Bass.supportedNegativeKFunctor i).map
      ((boundedAboveFlatCoefficientSupportedLaurentIso f).hom.app a) ≫
      Bass.supportedNegativeKπ ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj
        a).unop i ≫
        (boundedAboveFlatCoefficientSupportedNegativeKComparison f (i + 1)).hom.app a =
    (boundedAboveFlatCoefficientSupportedNegativeKComparison f i).hom.app
        ((laurentUnderFunctor R).obj a) ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        (mappingConeInclusion (StrictSquare.comparison
          ((boundedAboveFlatCoefficientSupportedBassDiagram f i).mapArrow.mapArrow.obj
            (laurentUnderSquare R a)))) ≫
        (KTheory.Bass.modelDiagramBottomSuccessorIso
          (boundedAboveFlatCoefficientSupportedModelFunctor f) i).inv.app a := by
  rw [boundedAboveFlatCoefficientSupportedNegativeKComparison_π,
    boundedAboveFlatCoefficientSupportedBassBottomContractionIso_π]


attribute [colib_ref "quillen" "CoefficientSupportedNegativeBottomComparison.lean:39"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedNegativeKComparison
attribute [colib_ref "quillen" "CoefficientSupportedNegativeBottomComparison.lean:51"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedNegativeKComparison_π
attribute [colib_ref "quillen" "CoefficientSupportedNegativeBottomComparison.lean:89"
  "adaptation" "Original supported finite-bottom comparison and actual quotient naturality"]
  boundedAboveFlatCoefficientSupportedNegativeKComparison_π_cone

end AlgebraicGeometry.Scheme.Modules
