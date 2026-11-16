/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenCofinality
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedOpenModels
public import Colib.KTheory.Waldhausen.Iterated.SmallModelComparison

/-! # The original perfect supported groups at the three auxiliary endpoints

These are original supported evaluation followed by the original perfect inclusion.
Only compactness of the ambient schemes is needed, not compactness of the support opens.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
CoefficientAuxiliaryPerfectClasses.lean`, revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory

universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The original fiber evaluation and perfect inclusion, with the union support unchanged. -/
def auxiliaryFiberPerfectKEquiv [CompactSpace Q.left] (a : Under R) (n : ℕ) :
    (boundedAboveFlatCoefficientSupportedFiberModel f T a).obj.waldhausen.K n ≃*
      PerfectSupportedK (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι n := by
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  exact (boundedAboveFlatCoefficientSupportedSectionKEquiv
    (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι n).trans
    (boundedAboveFlatPerfectSupportedKEquiv (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι n)

/-- The original ambient supported evaluation and perfect inclusion. -/
def auxiliaryAmbientPerfectKEquiv [CompactSpace Q.left] (a : Under R) (n : ℕ) :
    (boundedAboveFlatCoefficientSupportedAmbientModel T a).obj.waldhausen.K n ≃*
      PerfectSupportedK (boundedAboveFlatCoefficientSupportOpen Q T a).ι n := by
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  exact (boundedAboveFlatCoefficientSupportedSectionKEquiv
    (boundedAboveFlatCoefficientSupportOpen Q T a).ι n).trans
    (boundedAboveFlatPerfectSupportedKEquiv (boundedAboveFlatCoefficientSupportOpen Q T a).ι n)

/-- The original full-open perfect comparison retains the inverse-image support. -/
def auxiliaryOpenPerfectKEquiv [CompactSpace P.left] (a : Under R) (n : ℕ) :
    (boundedAboveFlatCoefficientSupportedFullOpenModel f T a).obj.waldhausen.K n ≃*
      PerfectSupportedK (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι n :=
  boundedAboveFlatCoefficientSupportedFullOpenPerfectKEquiv f T a n

/-- Original fiber perfect classes in the unchanged fine model spectrum. -/
def auxiliaryFiberPerfectStableEquiv [CompactSpace Q.left] (a : Under R) (n : ℕ) :=
  (auxiliaryFiberPerfectKEquiv f T a n).symm.toAdditive.trans
    (smallModelKStableEquiv (boundedAboveFlatCoefficientSupportedFiberModel f T a) n)

/-- Original ambient perfect classes in the unchanged fine model spectrum. -/
def auxiliaryAmbientPerfectStableEquiv [CompactSpace Q.left] (a : Under R) (n : ℕ) :=
  (auxiliaryAmbientPerfectKEquiv T a n).symm.toAdditive.trans
    (smallModelKStableEquiv (boundedAboveFlatCoefficientSupportedAmbientModel T a) n)

/-- Original full-open perfect classes in the unchanged fine model spectrum. -/
def auxiliaryOpenPerfectStableEquiv [CompactSpace P.left] (a : Under R) (n : ℕ) :=
  (auxiliaryOpenPerfectKEquiv f T a n).symm.toAdditive.trans
    (smallModelKStableEquiv (boundedAboveFlatCoefficientSupportedFullOpenModel f T a) n)

/-- Evaluation retains every original fiber model representative. -/
theorem auxiliaryFiberPerfectStableEquiv_evaluation [CompactSpace Q.left]
    (a : Under R) (n : ℕ)
    (x : (boundedAboveFlatCoefficientSupportedFiberModel f T a).obj.waldhausen.K n) :
    auxiliaryFiberPerfectStableEquiv f T a n
        (Additive.ofMul (auxiliaryFiberPerfectKEquiv f T a n x)) =
      smallModelKStableEquiv (boundedAboveFlatCoefficientSupportedFiberModel f T a) n
        (Additive.ofMul x) := by
  change smallModelKStableEquiv _ n (Additive.ofMul
    ((auxiliaryFiberPerfectKEquiv f T a n).symm
      (auxiliaryFiberPerfectKEquiv f T a n x))) = _
  rw [MulEquiv.symm_apply_apply]

/-- Evaluation retains every original ambient model representative. -/
theorem auxiliaryAmbientPerfectStableEquiv_evaluation [CompactSpace Q.left]
    (a : Under R) (n : ℕ)
    (x : (boundedAboveFlatCoefficientSupportedAmbientModel T a).obj.waldhausen.K n) :
    auxiliaryAmbientPerfectStableEquiv T a n
        (Additive.ofMul (auxiliaryAmbientPerfectKEquiv T a n x)) =
      smallModelKStableEquiv (boundedAboveFlatCoefficientSupportedAmbientModel T a) n
        (Additive.ofMul x) := by
  change smallModelKStableEquiv _ n (Additive.ofMul
    ((auxiliaryAmbientPerfectKEquiv T a n).symm
      (auxiliaryAmbientPerfectKEquiv T a n x))) = _
  rw [MulEquiv.symm_apply_apply]

omit [IsOpenImmersion f.left] in
/-- Evaluation retains every original full-open model representative. -/
theorem auxiliaryOpenPerfectStableEquiv_evaluation [CompactSpace P.left]
    (a : Under R) (n : ℕ)
    (x : (boundedAboveFlatCoefficientSupportedFullOpenModel f T a).obj.waldhausen.K n) :
    auxiliaryOpenPerfectStableEquiv f T a n
        (Additive.ofMul (auxiliaryOpenPerfectKEquiv f T a n x)) =
      smallModelKStableEquiv (boundedAboveFlatCoefficientSupportedFullOpenModel f T a) n
        (Additive.ofMul x) := by
  change smallModelKStableEquiv _ n (Additive.ofMul
    ((auxiliaryOpenPerfectKEquiv f T a n).symm
      (auxiliaryOpenPerfectKEquiv f T a n x))) = _
  rw [MulEquiv.symm_apply_apply]

end AlgebraicGeometry.Scheme.Modules
