/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassOriginalNegativeNaturality

/-!
Regression consumers for the original finite-stage comparison in every negative degree.
These statements retain the original Laurent representative and arbitrary scheme pullback.
They do not require or assert a comparison with the infinite telescope.
-/

open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
open CommRingCat.PolynomialLaurent

universe u
noncomputable section

example {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left] (i : ℕ) :
    boundedAboveFlatCoefficientQuasiCompactRow P ⋙ Scheme.Bass.negativeKFunctor i ≅
      boundedAboveFlatCoefficientAmbientBassDiagram P i ⋙ stableHomotopyFunctor (-(i : ℤ)) :=
  boundedAboveFlatCoefficientAmbientNegativeKComparison P i

example {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]
    (i : ℕ) (a : Under R) :
    (Scheme.Bass.negativeKFunctor i).map
        ((boundedAboveFlatCoefficientLaurentIso P).hom.app a) ≫
      Scheme.Bass.negativeKπ ((boundedAboveFlatCoefficientQuasiCompactRow P).obj a).unop i ≫
        (boundedAboveFlatCoefficientAmbientNegativeKComparison P (i + 1)).hom.app a =
    (boundedAboveFlatCoefficientAmbientNegativeKComparison P i).hom.app
        ((laurentUnderFunctor R).obj a) ≫
      (KTheory.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
        (boundedAboveFlatCoefficientAmbientBassDiagram P i ⋙
          stableHomotopyFunctor (-(i : ℤ)))).app a ≫
        (boundedAboveFlatCoefficientAmbientBassBottomContractionIso P i).hom.app a :=
  boundedAboveFlatCoefficientAmbientNegativeKComparison_π P i a

example {R : CommRingCat.{u}} {P Q : Over (Spec R)}
    [CompactSpace P.left] [CompactSpace Q.left] (f : P ⟶ Q) (i : ℕ) :
    boundedAboveFlatCoefficientOriginalNegativeKRestriction f i ≫
      (boundedAboveFlatCoefficientAmbientNegativeKComparison P i).hom =
    (boundedAboveFlatCoefficientAmbientNegativeKComparison Q i).hom ≫
      boundedAboveFlatCoefficientAmbientBassBottomSchemeRestriction f i :=
  boundedAboveFlatCoefficientAmbientNegativeKComparison_schemeRestriction f i

end
