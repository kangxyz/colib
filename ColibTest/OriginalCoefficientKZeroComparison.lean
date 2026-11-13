/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassKZeroComparison

/-! Consumers of original stage-zero class maps and arbitrary coefficient naturality. -/

open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.BaseChange.Coefficients

universe u
noncomputable section

example (R : CommRingCat.{u}) (P : Over (Spec R)) [CompactSpace P.left] :
    boundedAboveFlatCoefficientQuasiCompactRow P ⋙ Scheme.Bass.perfectKZeroFunctor ≅
      boundedAboveFlatCoefficientAmbientBassDiagram P 0 ⋙ stableHomotopyFunctor 0 :=
  boundedAboveFlatCoefficientAmbientBassBottomZeroNatIso P

example {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left] (a : Under R) :
    (boundedAboveFlatCoefficientAmbientBassBottomZeroNatIso P).hom.app a ≫
      (stableHomotopyFunctor 0).map
        (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op P, a)) =
      (perfectKZeroLocalizedStableIso ((boundedAboveFlatCoefficientQuasiCompactRow P).obj a)).hom :=
  boundedAboveFlatCoefficientAmbientBassBottomZeroNatIso_evaluation P a

example {R : CommRingCat.{u}} {i k : Index R} (f : i ⟶ k) :
    (boundedAboveFlatCoefficientSectionLocalizedSpectrumFunctor R).map f ≫
        (boundedAboveFlatCoefficientSectionEvaluationLocalizedIso k).hom =
      (boundedAboveFlatCoefficientSectionEvaluationLocalizedIso i).hom ≫
        boundedAboveFlatLocalizedPullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f) :=
  boundedAboveFlatCoefficientSectionEvaluationLocalizedIso_naturality f

end
