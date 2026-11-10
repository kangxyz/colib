/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.Sequence.Regular.SplitBaseChange

/-! # Direct consumers of arbitrary base change for a split regular quotient -/

open TensorProduct RingTheory.Sequence

variable {A B A' D : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [CommRing A'] [Algebra A A'] [CommRing D]
  [IsLocalRing B] [IsLocalRing D] [IsNoetherianRing D]

example (ε : B →ₐ[A] A) : Module.Flat A (B ⧸ RingHom.ker ε.toRingHom) :=
  flat_quotient_ker_algebraRetraction ε

example (ε : B →ₐ[A] A) {r : ℕ} (s : Fin r → B)
    (hs : IsRegular B (List.ofFn s))
    (hker : Ideal.span (Set.range s) = RingHom.ker ε.toRingHom)
    (q : B →+* D) [IsLocalHom q] (φ : B ⊗[A] A' →+* D)
    (hφ : φ.comp Algebra.TensorProduct.includeLeftRingHom = q)
    (hloc : letI : Algebra (B ⊗[A] A') D := φ.toAlgebra
      ∃ M : Submonoid (B ⊗[A] A'), IsLocalization M D) :
    IsRegular D (List.ofFn (fun i => q (s i))) :=
  hs.map_of_algebraRetraction_tensor_localization ε hker q φ hφ hloc

example {r : ℕ} (s : Fin r → B) (hs : IsRegular B (List.ofFn s)) (e : B ≃+* D) :
    IsRegular D (List.ofFn (fun i => e (s i))) := by
  simpa only [List.map_ofFn, Function.comp_def] using hs.map_ringEquiv e
