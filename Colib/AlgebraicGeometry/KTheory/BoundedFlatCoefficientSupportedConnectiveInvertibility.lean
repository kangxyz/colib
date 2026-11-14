/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAmbientConnectiveInvertibility
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenBassSeedRange

/-! # Connective invertibility of the original supported Bass seed -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The actual supported Bass seed is invertible in every connective degree. -/
instance boundedAboveFlatCoefficientSupportedBassTransition_zero_isIso (a : Under R) (n : ℕ) :
    IsIso ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedAboveFlatCoefficientSupportedBassTransition f 0).app a)) := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  exact boundedAboveFlatCoefficientSupportedBassTransition_zero_isIso_of_two_ambient f a n
    (fun j => boundedAboveFlatCoefficientAmbientBassTransition_zero_isIso P a j)
    (fun j => boundedAboveFlatCoefficientAmbientBassTransition_zero_isIso Q a j)

end AlgebraicGeometry.Scheme.Modules
