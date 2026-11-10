/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# The actual uniformizer exponent square

Adapted from `Aglib/KTheory/MilnorK/Norm/Polynomial/DVRCoprimeBaseChange.lean`
at revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 47–66.
The native additive valuation proves equality of the two exponents directly.
No fraction field, norm square, coprimality, or cancellation in a Milnor group is needed.
-/

@[expose] public noncomputable section

namespace IsDiscreteValuationRing

/-- Both literal paths around a commuting ring square have the same uniformizer exponent. -/
theorem ramification_square_of_uniformizer_equations
    {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T]
    [CommRing U] [IsDomain U] [IsDiscreteValuationRing U]
    (j : R →+* S) (k : R →+* T) (l : S →+* U) (m : T →+* U)
    (hcomm : l.comp j = m.comp k)
    {π : R} {ϖ : S} {τ : T} {ρ : U} (hρ : Irreducible ρ)
    (u : Sˣ) (v : Tˣ) (w z : Uˣ) (e a b c : ℕ)
    (he : j π = (u : S) * ϖ ^ e) (ha : k π = (v : T) * τ ^ a)
    (hb : l ϖ = (w : U) * ρ ^ b) (hc : m τ = (z : U) * ρ ^ c) :
    e * b = a * c := by
  have h : (↑(Units.map l.toMonoidHom u * w ^ e) : U) * ρ ^ (e * b) =
      (↑(Units.map m.toMonoidHom v * z ^ a) : U) * ρ ^ (a * c) := by
    change (l (u : S) * (w : U) ^ e) * ρ ^ (e * b) =
      (m (v : T) * (z : U) ^ a) * ρ ^ (a * c)
    have hmaps := RingHom.congr_fun hcomm π
    change l (j π) = m (k π) at hmaps
    simpa only [he, ha, map_mul, map_pow, hb, hc, mul_pow, ← pow_mul,
      mul_assoc, Nat.mul_comm] using hmaps
  have hv := congrArg (addVal U) h
  rw [addVal_def' _ hρ, addVal_def' _ hρ] at hv
  exact_mod_cast hv

end IsDiscreteValuationRing

end
