/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.Tor.LocalizedMiddleDiagonal
public import Mathlib.RingTheory.Length

/-!
# Length of the actual localized middle-diagonal Tor modules

The actual localized middle-diagonal quotient is surjective. Mathlib's
`Module.length_eq_of_surjective` therefore compares the module lengths over the two actual
prime-localized rings. Length takes values in `ℕ∞`, and this result needs no finite-length
hypothesis. Any later Euler sum still requires actual finiteness and finite degree support.

The restriction-of-scalars wrapper is adapted from `motivic_source_a6805c4`,
`Motivic/Aglib/Algebra/Category/ModuleCat/Tor/AmbientLength.lean`,
`ModuleCat.length_restrictScalars_of_surjective`. The localized Tor comparison itself is
constructed in `LocalizedMiddleDiagonal`, not an input assumption.

## References

* Stacks Project, Tag 00IX, part (2): equality of length under a surjective ring map.
* Stacks Project, Tag 00M8: flat base change for Tor.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace ModuleCat

/-- Literal restriction along a surjective ring map preserves actual module length. -/
theorem length_restrictScalars_of_surjective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (M : ModuleCat.{u} S) :
    Module.length R ((ModuleCat.restrictScalars f).obj M) = Module.length S M := by
  let := f.toAlgebra
  let : IsScalarTower R S ((ModuleCat.restrictScalars f).obj M) := ⟨fun r s x ↦ by
    change (f r * s) • x = f r • (s • x)
    exact mul_smul (f r) s x⟩
  exact Module.length_eq_of_surjective (R := S)
    (M := (ModuleCat.restrictScalars f).obj M) hf

namespace Tor

open Algebra.TensorProduct.MiddleDiagonal

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
variable (q : Ideal (tripleRing k A B C)) [q.IsPrime]

/-- The ring structure on the localized triple ring, projected from its commutative ring. -/
local instance : Ring (Localization.AtPrime q) :=
  (inferInstance : CommRing (Localization.AtPrime q)).toRing

/-- The ring structure at the induced ambient prime, projected from its commutative ring. -/
local instance : Ring (Localization.AtPrime (ambientPrime k A B C q)) :=
  (inferInstance : CommRing (Localization.AtPrime (ambientPrime k A B C q))).toRing

/-- Equality of actual Tor lengths at the induced prime, with no finiteness assumption and
no additional surjectivity hypothesis. -/
theorem middleDiagonalTorAtPrime_length (I : Ideal (A ⊗[k] B))
    (J : Ideal (B ⊗[k] C)) (n : ℕ) :
    Module.length (Localization.AtPrime (ambientPrime k A B C q))
      (middleDiagonalTorAtPrime k A B C q I J n) =
    Module.length (Localization.AtPrime q) (middleSupportTorAtPrime k A B C q I J n) := by
  have h₁ := (middleDiagonalTorAtPrimeIso k A B C q I J n).toLinearEquiv.length_eq
  have h₂ := ModuleCat.length_restrictScalars_of_surjective
    (R := Localization.AtPrime (ambientPrime k A B C q)) (S := Localization.AtPrime q)
    (localizedQuotientMap k A B C q) (localizedQuotientMap_surjective k A B C q)
    (middleSupportTorAtPrime k A B C q I J n)
  exact h₁.trans h₂

/-- Finite length transfers in either direction; neither side is claimed universally finite. -/
theorem middleDiagonalTorAtPrime_length_lt_top_iff (I : Ideal (A ⊗[k] B))
    (J : Ideal (B ⊗[k] C)) (n : ℕ) :
    Module.length (Localization.AtPrime (ambientPrime k A B C q))
        (middleDiagonalTorAtPrime k A B C q I J n) < ⊤ ↔
      Module.length (Localization.AtPrime q) (middleSupportTorAtPrime k A B C q I J n) < ⊤ := by
  rw [middleDiagonalTorAtPrime_length]

end Tor

end ModuleCat
