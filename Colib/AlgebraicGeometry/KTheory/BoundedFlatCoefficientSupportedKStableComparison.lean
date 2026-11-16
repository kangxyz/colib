/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedKZeroComparison

/-!
# Original supported K-groups in the same native fine section spectrum

Original supported evaluation and the actual model K/stable equivalence give the
comparison in every nonnegative degree, naturally for each original coefficient
pair pullback. The comparison retains the original perfect K-groups and the
unchanged fine section prespectrum. Only ambient compactness is required here.
Compatibility with degree-raising scalar self-track operations requires an actual
unit-preserving evaluation square and is not a consequence of this ordinary-map
naturality theorem.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
CoefficientSupportedKStableComparison.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- Original supported K-theory computes the same actual fine section stable group. -/
def boundedAboveFlatCoefficientSupportedKStableEquiv (a : Under R) (n : ℕ) :
    Additive (PerfectSupportedK (schemeMap f a) n) ≃+
      stableHomotopyGroup ((boundedAboveFlatCoefficientSupportedPrespectrumFunctor f).obj a)
        (n : ℤ) :=
  (boundedAboveFlatCoefficientSupportedPerfectKEquiv f a n).symm.toAdditive.trans
    (smallModelKStableEquiv (boundedAboveFlatCoefficientSupportedModel f a) n)

/-- The original evaluation representative maps to the original model stable representative. -/
theorem boundedAboveFlatCoefficientSupportedKStableEquiv_evaluation (a : Under R) (n : ℕ)
    (x : (boundedAboveFlatCoefficientSupportedModel f a).obj.waldhausen.K n) :
    boundedAboveFlatCoefficientSupportedKStableEquiv f a n
        (Additive.ofMul (boundedAboveFlatCoefficientSupportedPerfectKEquiv f a n x)) =
      smallModelKStableEquiv (boundedAboveFlatCoefficientSupportedModel f a) n
        (Additive.ofMul x) := by
  change smallModelKStableEquiv (boundedAboveFlatCoefficientSupportedModel f a) n
    (Additive.ofMul ((boundedAboveFlatCoefficientSupportedPerfectKEquiv f a n).symm
      (boundedAboveFlatCoefficientSupportedPerfectKEquiv f a n x))) = _
  rw [MulEquiv.symm_apply_apply]

/-- Naturality preserves the original coefficient pair pullback and unchanged model map. -/
theorem boundedAboveFlatCoefficientSupportedKStableEquiv_naturality
    {a b : Under R} (g : a ⟶ b) (n : ℕ) (x : PerfectSupportedK (schemeMap f a) n) :
    boundedAboveFlatCoefficientSupportedKStableEquiv f b n
      (Additive.ofMul (perfectSupportedKPullback
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).map g).unop n x)) =
    (stableHomotopyFunctor (n : ℤ)).map
      ((boundedAboveFlatCoefficientSupportedPrespectrumFunctor f).map g)
      (boundedAboveFlatCoefficientSupportedKStableEquiv f a n (Additive.ofMul x)) := by
  obtain ⟨y, rfl⟩ := (boundedAboveFlatCoefficientSupportedPerfectKEquiv f a n).surjective x
  rw [← boundedAboveFlatCoefficientSupportedPerfectKEquiv_naturality,
    boundedAboveFlatCoefficientSupportedKStableEquiv_evaluation,
    boundedAboveFlatCoefficientSupportedKStableEquiv_evaluation]
  exact smallModelKStableEquiv_naturality (boundedAboveFlatCoefficientSupportedModelMap f g) n y

/-- Degree zero is exactly the established comparison used by the original negative recursion. -/
theorem boundedAboveFlatCoefficientSupportedKStableEquiv_zero (a : Under R)
    (x : PerfectSupportedK (schemeMap f a) 0) :
    boundedAboveFlatCoefficientSupportedKStableEquiv f a 0 (Additive.ofMul x) =
      (boundedAboveFlatCoefficientSupportedBassBottomZeroIso f a).hom (Additive.ofMul x) := rfl

end AlgebraicGeometry.Scheme.Modules
