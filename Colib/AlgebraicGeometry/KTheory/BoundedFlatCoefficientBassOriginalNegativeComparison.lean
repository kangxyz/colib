/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassKZeroComparison
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientPolynomialLaurentTransport
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassBottomComparison

/-!
Source:
Quillen source module
`AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassOriginalNegativeComparison.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Original scheme negative K-groups at native finite-stage bottoms

The original scheme Bass recursion is compared with the actual native finite
Model stages. Genuine natural polynomial/Laurent product isomorphisms and the
original K-zero evaluation determine the comparison in every negative degree.
The ambient scheme is compact, and the assembled induction is natural in the
coefficient ring arrows. Supported groups and scheme-restriction naturality of the
assembled induction are outside this interface. No seed invertibility, transition
stability, telescope identification or classical TT identification is asserted.
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
variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]

/-- The original scheme groups are naturally the bottom groups of every native finite stage. -/
def boundedAboveFlatCoefficientAmbientNegativeKComparison :
    (i : ℕ) → boundedAboveFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor i ≅
      boundedAboveFlatCoefficientAmbientBassDiagram P i ⋙ stableHomotopyFunctor (-(i : ℤ))
  | 0 => boundedAboveFlatCoefficientAmbientBassBottomZeroNatIso P
  | i + 1 =>
      (boundedAboveFlatCoefficientContractionTransportIso P (Bass.negativeKFunctor i)).symm ≪≫
      (KTheory.Bass.TwoChart.contractionFunctor (underToLaurent R) (underToLaurentInvert R)).mapIso
        (boundedAboveFlatCoefficientAmbientNegativeKComparison i) ≪≫
      boundedAboveFlatCoefficientAmbientBassBottomContractionIso P i

/-- Every original Laurent representative is preserved through the genuine product transport. -/
@[reassoc]
theorem boundedAboveFlatCoefficientAmbientNegativeKComparison_π (i : ℕ) (a : Under R) :
    (Bass.negativeKFunctor i).map ((boundedAboveFlatCoefficientLaurentIso P).hom.app a) ≫
      Bass.negativeKπ ((boundedAboveFlatCoefficientQuasiCompactRow P).obj a).unop i ≫
        (boundedAboveFlatCoefficientAmbientNegativeKComparison P (i + 1)).hom.app a =
    (boundedAboveFlatCoefficientAmbientNegativeKComparison P i).hom.app
        ((laurentUnderFunctor R).obj a) ≫
      (KTheory.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
        (boundedAboveFlatCoefficientAmbientBassDiagram P i ⋙
          stableHomotopyFunctor (-(i : ℤ)))).app a ≫
        (boundedAboveFlatCoefficientAmbientBassBottomContractionIso P i).hom.app a := by
  let τ := boundedAboveFlatCoefficientContractionTransportIso P (Bass.negativeKFunctor i)
  let γ := boundedAboveFlatCoefficientAmbientNegativeKComparison P i
  let β := boundedAboveFlatCoefficientAmbientBassBottomContractionIso P i
  have ht : (KTheory.Bass.TwoChart.contractionπ (underToLaurent R)
      (underToLaurentInvert R)
      (boundedAboveFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor i)).app a ≫
      τ.hom.app a =
    (Bass.negativeKFunctor i).map ((boundedAboveFlatCoefficientLaurentIso P).hom.app a) ≫
      Bass.negativeKπ ((boundedAboveFlatCoefficientQuasiCompactRow P).obj a).unop i :=
    boundedAboveFlatCoefficientContractionTransportIso_π P (Bass.negativeKFunctor i) a
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

end AlgebraicGeometry.Scheme.Modules
