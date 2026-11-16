/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientConnectiveGroups

/-! # Representatives of the original coefficient connective comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen.IteratedS Opposite
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Topology.LoopPrespectrum

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Evaluation sends each stable connective coefficient class to its original K-class. -/
@[reassoc]
theorem boundedAboveFlatCoefficientAmbientBassConnectiveNatIso_evaluation
    {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left] (n : ℕ) (a : Under R) :
    (boundedAboveFlatCoefficientAmbientBassConnectiveNatIso P n).hom.app a ≫
      (stableHomotopyFunctor (n : ℤ)).map
        (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op P, a)) =
    (connectivePerfectKLocalizedStableIso n
      ((boundedAboveFlatCoefficientQuasiCompactRow P).obj a)).hom := by
  let A := Functor.isoWhiskerLeft (boundedAboveFlatCoefficientQuasiCompactRow P)
    (connectivePerfectKLocalizedStableNatIso n)
  let E := Functor.isoWhiskerRight
    (boundedAboveFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso P)
    (localizedStableHomotopyFunctor (n : ℤ))
  have hE : E.hom.app a = (stableHomotopyFunctor (n : ℤ)).map
      (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op P, a)) := by
    simp only [E, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      boundedAboveFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso_hom_app]
    exact localizedStableHomotopyFunctor_original_map _ _
  change (A.hom.app a ≫ E.inv.app a) ≫ _ = _
  calc
    _ = A.hom.app a ≫ E.inv.app a ≫ E.hom.app a :=
      (Category.assoc _ _ _).trans
        (congrArg (fun t => A.hom.app a ≫ E.inv.app a ≫ t) hE.symm)
    _ = _ := by
      rw [← NatTrans.comp_app, E.inv_hom_id, NatTrans.id_app]
      exact Category.comp_id (A.hom.app a)

end AlgebraicGeometry.Scheme.Modules
