/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedBassTransitionNaturality
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenConeStable
public import Colib.Topology.Prespectrum.ConeStableRangeDetection

/-! # Detection of the supported cone transition by the actual open transition

This uses the original cone-to-open stable equivalences and their strict naturality.
The two lemmas are reductions, not unconditional invertibility of the supported Bass seed.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
CoefficientSupportedConnectiveInvertibility.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- The original cone transition is invertible in positive degrees through its actual descents.
-/
theorem boundedAboveFlatCoefficientSupportedBassConeTransition_zero_isIso_of_open
    (a : Under R) (d : ℤ)
    (h : IsIso ((stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientOpenBassTransition f 0).app a))) :
    IsIso ((stableHomotopyFunctor d).map
      (mappingConeMap (boundedAboveFlatCoefficientSupportedBassTransitionSquare f 0 a))) := by
  let e₀ := (boundedAboveFlatCoefficientSupportedBassOpenConeMap f 0).app a
  let e₁ := (boundedAboveFlatCoefficientSupportedBassOpenConeMap f 1).app a
  let c := mappingConeMap (boundedAboveFlatCoefficientSupportedBassTransitionSquare f 0 a)
  let τC := (boundedAboveFlatCoefficientOpenBassTransition f 0).app a
  let : IsIso ((stableHomotopyFunctor d).map e₀) :=
    boundedAboveFlatCoefficientSupportedBassOpenConeMap_isStableEquivalence f 0 a d
  let : IsIso ((stableHomotopyFunctor d).map e₁) :=
    boundedAboveFlatCoefficientSupportedBassOpenConeMap_isStableEquivalence f 1 a d
  let : IsIso ((stableHomotopyFunctor d).map τC) :=
    h
  have he := congrArg ((stableHomotopyFunctor d).map)
    (boundedAboveFlatCoefficientSupportedBassOpenConeMap_transition f 0 a)
  change (stableHomotopyFunctor d).map (c ≫ e₁) =
    (stableHomotopyFunctor d).map (e₀ ≫ τC) at he
  simp only [Functor.map_comp] at he
  let : IsIso ((stableHomotopyFunctor d).map c ≫ (stableHomotopyFunctor d).map e₁) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((stableHomotopyFunctor d).map e₁)

/-- At degree zero only the honest coarse injectivity is needed for the original cone transition.
-/
theorem boundedAboveFlatCoefficientSupportedBassConeTransition_zero_injective_of_open
    (a : Under R)
    (h₀ : Function.Injective ((stableHomotopyFunctor 0).map
      ((boundedAboveFlatCoefficientOpenBassTransition f 0).app a))) :
    Function.Injective ((stableHomotopyFunctor 0).map
      (mappingConeMap (boundedAboveFlatCoefficientSupportedBassTransitionSquare f 0 a))) := by
  let e₀ := (boundedAboveFlatCoefficientSupportedBassOpenConeMap f 0).app a
  let e₁ := (boundedAboveFlatCoefficientSupportedBassOpenConeMap f 1).app a
  let c := mappingConeMap (boundedAboveFlatCoefficientSupportedBassTransitionSquare f 0 a)
  let τC := (boundedAboveFlatCoefficientOpenBassTransition f 0).app a
  let : IsIso ((stableHomotopyFunctor 0).map e₀) :=
    boundedAboveFlatCoefficientSupportedBassOpenConeMap_isStableEquivalence f 0 a 0
  have he := congrArg ((stableHomotopyFunctor 0).map)
    (boundedAboveFlatCoefficientSupportedBassOpenConeMap_transition f 0 a)
  change (stableHomotopyFunctor 0).map (c ≫ e₁) =
    (stableHomotopyFunctor 0).map (e₀ ≫ τC) at he
  simp only [Functor.map_comp] at he
  intro x y h
  apply (ConcreteCategory.bijective_of_isIso ((stableHomotopyFunctor 0).map e₀)).injective
  apply h₀
  exact (ConcreteCategory.congr_hom he x).symm.trans
    ((congrArg ((stableHomotopyFunctor 0).map e₁) h).trans
      (ConcreteCategory.congr_hom he y))

/-- The actual supported seed is invertible when its ambient and open arrows have
the requisite stable range. The open arrow needs only injectivity at degree zero. -/
theorem boundedAboveFlatCoefficientSupportedBassTransition_zero_isIso_of_ambient_open
    (a : Under R) (n : ℕ)
    (hA : ∀ j : ℕ, IsIso ((stableHomotopyFunctor (j : ℤ)).map
      ((boundedAboveFlatCoefficientAmbientBassTransition Q 0).app a)))
    (hC : ∀ d : ℤ, 0 < d → IsIso ((stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientOpenBassTransition f 0).app a)))
    (hC₀ : Function.Injective ((stableHomotopyFunctor 0).map
      ((boundedAboveFlatCoefficientOpenBassTransition f 0).app a))) :
    IsIso ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedAboveFlatCoefficientSupportedBassTransition f 0).app a)) := by
  apply left_stableMap_isIso_of_coneMap
    (boundedAboveFlatCoefficientSupportedBassTransitionSquare f 0 a)
    (boundedAboveFlatCoefficientSupportedBassForget_coneFiber_isStableEquivalence f 0 a)
    (boundedAboveFlatCoefficientSupportedBassForget_coneFiber_isStableEquivalence f 1 a) (n : ℤ)
  · have he : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
    rw [he]
    let := hA (n + 1)
    exact (ConcreteCategory.bijective_of_isIso
      ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
        ((boundedAboveFlatCoefficientAmbientBassTransition Q 0).app a))).surjective
  · exact (ConcreteCategory.isIso_iff_bijective _).mp
      (boundedAboveFlatCoefficientSupportedBassConeTransition_zero_isIso_of_open f a
        ((n : ℤ) + 1) (hC _ (by omega)))
  · let := hA n
    exact ConcreteCategory.bijective_of_isIso
      ((stableHomotopyFunctor (n : ℤ)).map
        ((boundedAboveFlatCoefficientAmbientBassTransition Q 0).app a))
  · cases n with
    | zero =>
      exact boundedAboveFlatCoefficientSupportedBassConeTransition_zero_injective_of_open f a hC₀
    | succ n => exact ((ConcreteCategory.isIso_iff_bijective _).mp
        (boundedAboveFlatCoefficientSupportedBassConeTransition_zero_isIso_of_open f a
          ((n + 1 : ℕ) : ℤ) (hC _ (by omega)))).injective

end AlgebraicGeometry.Scheme.Modules
