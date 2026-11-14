/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenBassFirstComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedConeTransitionDetection

/-!
# Transfer of the connective Bass seed along restriction

Positive-degree invertibility transfers to the original coarse open seed. In degree
zero the comparison only gives injectivity, since coarse restriction need not be
surjective. The fine seed is the original strict transition on the open scheme.

Source: `CoefficientOpenConnectiveInvertibility.lean` in
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

variable (a : Under R)
  (hFine : ∀ n : ℕ, IsIso ((stableHomotopyFunctor (n : ℤ)).map
    ((boundedAboveFlatCoefficientFullOpenBassTransition f 0).app a)))

include hFine in
/-- The actual coarse-open stage-zero seed is invertible in each positive degree. -/
theorem boundedAboveFlatCoefficientOpenBassTransition_zero_positive_isIso
    (d : ℤ) (hd : 0 < d) :
    IsIso ((stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientOpenBassTransition f 0).app a)) := by
  let r₀ := (boundedAboveFlatCoefficientOpenBassRestriction f 0).app a
  let r₁ := (boundedAboveFlatCoefficientOpenBassRestriction f 1).app a
  let τC := (boundedAboveFlatCoefficientOpenBassTransition f 0).app a
  let τF := (boundedAboveFlatCoefficientFullOpenBassTransition f 0).app a
  let : IsIso ((stableHomotopyFunctor d).map r₀) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨boundedAboveFlatCoefficientOpenRestriction_stable_injective f a d,
        boundedAboveFlatCoefficientOpenRestriction_stable_surjective_of_ne_zero f a d (ne_of_gt hd)⟩
  let : IsIso ((stableHomotopyFunctor d).map r₁) :=
    boundedAboveFlatCoefficientOpenBassRestriction_one_positive_isIso f a d hd
  let : IsIso ((stableHomotopyFunctor d).map τF) := by
    have he : (d.toNat : ℤ) = d := Int.toNat_of_nonneg (le_of_lt hd)
    rw [← he]
    exact hFine d.toNat
  have hs : r₀ ≫ τF = τC ≫ r₁ :=
    NatTrans.congr_app (boundedAboveFlatCoefficientOpenBassRestriction_transition f 0) a
  have he := congrArg ((stableHomotopyFunctor d).map) hs
  simp only [Functor.map_comp] at he
  let : IsIso ((stableHomotopyFunctor d).map τC ≫ (stableHomotopyFunctor d).map r₁) := by
    rw [← he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((stableHomotopyFunctor d).map r₁)

include hFine in
/-- Zero-degree coarse seed injectivity uses the honest original restriction image only. -/
theorem boundedAboveFlatCoefficientOpenBassTransition_zero_stable_zero_injective :
    Function.Injective ((stableHomotopyFunctor 0).map
      ((boundedAboveFlatCoefficientOpenBassTransition f 0).app a)) := by
  let r₀ := (boundedAboveFlatCoefficientOpenBassRestriction f 0).app a
  let r₁ := (boundedAboveFlatCoefficientOpenBassRestriction f 1).app a
  let τC := (boundedAboveFlatCoefficientOpenBassTransition f 0).app a
  let τF := (boundedAboveFlatCoefficientFullOpenBassTransition f 0).app a
  let : IsIso ((stableHomotopyFunctor 0).map τF) :=
    hFine 0
  have hs : r₀ ≫ τF = τC ≫ r₁ :=
    NatTrans.congr_app (boundedAboveFlatCoefficientOpenBassRestriction_transition f 0) a
  have he := congrArg ((stableHomotopyFunctor 0).map) hs
  simp only [Functor.map_comp] at he
  intro x y h
  apply boundedAboveFlatCoefficientOpenRestriction_stable_injective f a 0
  apply (ConcreteCategory.bijective_of_isIso ((stableHomotopyFunctor 0).map τF)).injective
  exact (ConcreteCategory.congr_hom he x).trans
    ((congrArg ((stableHomotopyFunctor 0).map r₁) h).trans
      (ConcreteCategory.congr_hom he y).symm)

omit [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] in
/-- The original full-open seed is literally the ambient seed on the open scheme. -/
theorem boundedAboveFlatCoefficientFullOpenBassTransition_zero_isIso_of_ambient (n : ℕ)
    (hP : IsIso ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedAboveFlatCoefficientAmbientBassTransition P 0).app a))) :
    IsIso ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedAboveFlatCoefficientFullOpenBassTransition f 0).app a)) :=
  hP

/-- The actual supported seed follows from the ambient seed on both schemes. -/
theorem boundedAboveFlatCoefficientSupportedBassTransition_zero_isIso_of_two_ambient
    (n : ℕ)
    (hP : ∀ j : ℕ, IsIso ((stableHomotopyFunctor (j : ℤ)).map
      ((boundedAboveFlatCoefficientAmbientBassTransition P 0).app a)))
    (hQ : ∀ j : ℕ, IsIso ((stableHomotopyFunctor (j : ℤ)).map
      ((boundedAboveFlatCoefficientAmbientBassTransition Q 0).app a))) :
    IsIso ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedAboveFlatCoefficientSupportedBassTransition f 0).app a)) := by
  have h := fun j => boundedAboveFlatCoefficientFullOpenBassTransition_zero_isIso_of_ambient
    f a j (hP j)
  exact boundedAboveFlatCoefficientSupportedBassTransition_zero_isIso_of_ambient_open f a n hQ
    (boundedAboveFlatCoefficientOpenBassTransition_zero_positive_isIso f a h)
    (boundedAboveFlatCoefficientOpenBassTransition_zero_stable_zero_injective f a h)

end AlgebraicGeometry.Scheme.Modules
