/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassOriginalNegativeNaturality
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientFullOpenBassLocalization

/-!
# The ambient negative class map and full-open restriction

The actual finite-bottom class followed by its telescope inclusion respects
the full-open localization arrow. This compatibility does not require
invertibility of the ambient inclusion.
-/
@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]

/-- The original ambient class at the bottom degree enters the actual telescope. -/
def boundedAboveFlatCoefficientAmbientBassNegativeMap (i : ℕ) :
    boundedAboveFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor i ⟶
      boundedAboveFlatCoefficientAmbientBassTelescopeFunctor P ⋙
        stableHomotopyFunctor (-(i : ℤ)) :=
  (boundedAboveFlatCoefficientAmbientNegativeKComparison P i).hom ≫
    Functor.whiskerRight (boundedAboveFlatCoefficientAmbientBassTelescopeInclusion P i) _

variable {P} {Q : Over (Spec R)} [CompactSpace Q.left] (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- Pullback on the original groups gives actual full-open restriction on the telescope. -/
theorem boundedAboveFlatCoefficientAmbientBassNegativeMap_fullOpen (i : ℕ) :
    boundedAboveFlatCoefficientOriginalNegativeKRestriction f i ≫
      boundedAboveFlatCoefficientAmbientBassNegativeMap P i =
    boundedAboveFlatCoefficientAmbientBassNegativeMap Q i ≫
      Functor.whiskerRight (boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f)
        (stableHomotopyFunctor (-(i : ℤ))) := by
  apply NatTrans.ext
  funext a
  simp only [boundedAboveFlatCoefficientAmbientBassNegativeMap, NatTrans.comp_app,
    Functor.whiskerRight_app, ← Category.assoc]
  have h := NatTrans.congr_app
    (boundedAboveFlatCoefficientAmbientNegativeKComparison_schemeRestriction f i) a
  simp only [NatTrans.comp_app] at h
  rw [h, Category.assoc]
  let H := stableHomotopyFunctor (-(i : ℤ))
  change _ ≫ (H.map ((boundedAboveFlatCoefficientAmbientBassSchemeRestriction f i).app a) ≫
    H.map ((boundedAboveFlatCoefficientAmbientBassTelescopeInclusion P i).app a)) =
      _ ≫ (H.map ((boundedAboveFlatCoefficientAmbientBassTelescopeInclusion Q i).app a) ≫
        H.map ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a))
  simp only [← H.map_comp]
  have h' := boundedAboveFlatCoefficientAmbientBassTelescopeInclusion_fullOpen f i
  rw [boundedAboveFlatCoefficientAmbientBassFullOpen_eq_original] at h'
  exact congrArg (fun g => (boundedAboveFlatCoefficientAmbientNegativeKComparison Q i).hom.app a ≫
    H.map g) (NatTrans.congr_app h' a).symm

end AlgebraicGeometry.Scheme.Modules
