/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Iterated.ExactModelComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportConeStable
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenCofinality

/-!
# The original K-classes of the support localization evaluation square

The three literal chosen-zero evaluation Model arrows preserve their original
coefficient K-equivalences. The supported map is invertible in every nonnegative
degree by the actual evaluation equivalence, without a compactness hypothesis.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatCoefficientSupportedEvaluation
  boundedAboveFlatCoefficientSupportedSectionEquivalence
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The literal coarse evaluation retains the existing relative-open K-equivalence. -/
theorem openEvaluationModelMap_stable (a : Under R) (n : ℕ)
    (x : (boundedAboveFlatCoefficientOpenModel f a).obj.waldhausen.K n) :
    (stableHomotopyFunctor (n : ℤ)).map (prespectrumMap (openEvaluationModelMap f a))
        (smallModelKStableEquiv (boundedAboveFlatCoefficientOpenModel f a) n (Additive.ofMul x)) =
      originalKStableEquiv (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)) n
        (Additive.ofMul (boundedAboveFlatCoefficientOpenKEquiv f a n x)) := by
  have h := (smallModelKStableEquiv_naturality (openEvaluationModelMap f a) n x).symm
  change _ = originalKStableEquiv (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)) n
    (Additive.ofMul (((boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)).asSmallKEquiv n).symm
      (KMap (openEvaluationModelMap f a).hom.isExact n x)))
  change _ = smallModelKStableEquiv
    (asSmallCategory (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a))) n
    (Additive.ofMul ((boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)).asSmallKEquiv n
      (((boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)).asSmallKEquiv n).symm
        (KMap (openEvaluationModelMap f a).hom.isExact n x))))
  rw [MulEquiv.apply_symm_apply]
  exact h

end AlgebraicGeometry.Scheme.Modules
