/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.KTheory.PerfectSupportedExcisionSpectrum

/-! # Full-signature consumers for genuine supported open-cover excision -/

noncomputable section
open CategoryTheory CategoryTheory.Limits Waldhausen AlgebraicGeometry Topology
open AlgebraicGeometry.Scheme.Modules LoopPrespectrum Waldhausen.IteratedS
universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

example : perfectSupportedExtensionByZero j T hcover ⊣ perfectSupportedRestrict j T :=
  perfectSupportedExcisionAdjunction j T hcover

example (K : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory) :
    ((perfectSupportedExcisionUnit j T hcover).app K).hom =
      (Complex.extensionByZeroAdjunction j).unit.app K.obj := rfl

example (K : (perfectSupported T.ι).FullSubcategory) :
    ((perfectSupportedExcisionCounit j T hcover).app K).hom =
      (Complex.extensionByZeroAdjunction j).counit.app K.obj := rfl

example : (perfectSupportedExcisionRealizationHomotopyEquiv j T hcover).toFun =
    (deloopingMap (perfectSupportedRestrict_exact j T)).hom := rfl

example : (perfectSupportedExcisionRealizationHomotopyEquiv j T hcover).invFun =
    (deloopingMap (perfectSupportedExtensionByZero_exact j T hcover)).hom := rfl

example (n : ℕ) (x : PerfectSupportedK T.ι n) :
    perfectSupportedExcisionKEquiv j T hcover n x = perfectSupportedKRestrict j T n x := rfl

example (n : ℕ) (x : PerfectSupportedK (j ⁻¹ᵁ T).ι n) :
    (perfectSupportedExcisionKEquiv j T hcover n).symm x =
      KMap (perfectSupportedExtensionByZero_exact j T hcover) n x := rfl

example (x : PerfectSupportedK T.ι 0) :
    KMap (perfectSupportedExtensionByZero_exact j T hcover) 0
      (perfectSupportedKRestrict j T 0 x) = x :=
  perfectSupportedKRestrict_extensionByZero_leftInverse j T hcover 0 x

example (x : PerfectSupportedK (j ⁻¹ᵁ T).ι 0) :
    perfectSupportedKRestrict j T 0
      (KMap (perfectSupportedExtensionByZero_exact j T hcover) 0 x) = x :=
  perfectSupportedKRestrict_extensionByZero_rightInverse j T hcover 0 x

example (n : ℕ) : Function.Bijective (perfectSupportedKRestrict j T n) :=
  perfectSupportedKRestrict_bijective_of_cover j T hcover n

example : perfectSupportedExcisionPrespectrumMap j T =
    exactOriginalPrespectrumMap (perfectSupportedWaldhausen T.ι)
      (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) (perfectSupportedRestrict_exact j T) := rfl

example (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (perfectSupportedExcisionPrespectrumMap j T)) :=
  perfectSupportedExcisionPrespectrumMap_isStableEquivalence j T hcover d

example (n : ℕ) (x : PerfectSupportedK T.ι n) :
    originalKStableEquiv (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) n
        (Additive.ofMul (perfectSupportedKRestrict j T n x)) =
      (stableHomotopyFunctor (n : ℤ)).map (perfectSupportedExcisionPrespectrumMap j T)
        (originalKStableEquiv (perfectSupportedWaldhausen T.ι) n (Additive.ofMul x)) :=
  perfectSupportedExcisionPrespectrumMap_originalK_naturality j T n x

example (x : PerfectSupportedK T.ι 0) :
    originalKStableEquiv (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι) 0
        (Additive.ofMul (perfectSupportedKRestrict j T 0 x)) =
      (stableHomotopyFunctor (0 : ℤ)).map (perfectSupportedExcisionPrespectrumMap j T)
        (originalKStableEquiv (perfectSupportedWaldhausen T.ι) 0 (Additive.ofMul x)) :=
  perfectSupportedExcisionPrespectrumMap_originalK_naturality j T 0 x
