module

import Colib.AlgebraicGeometry.Intersection.TorFormula.LocalVanishing

/-! Newly reconstructed regression examples, 2026-11-08. Not compiled in this recovery.
The assumptions deliberately contain no coherence or global dimension bound. -/

open AlgebraicGeometry CategoryTheory

universe u

section

variable (X : Scheme.{u}) (F G : X.Modules) (x : X)
    [IsRegularLocalRing (X.presheaf.stalk x)]

example (d p : ℕ) (hdim : ringKrullDim (X.presheaf.stalk x) ≤ (d : WithBot ℕ∞))
    (hdp : d < p) :
    Module.length (X.presheaf.stalk x)
      ((TorFormula.torSheaf X F G p).presheaf.stalk x) = 0 :=
  TorFormula.length_stalk_torSheaf_eq_zero_of_lt X F G x d p hdim hdp

example : ∃ d : ℕ, ∀ (F G : X.Modules) (p : ℕ), d < p →
    Module.length (X.presheaf.stalk x)
      ((TorFormula.torSheaf X F G p).presheaf.stalk x) = 0 :=
  TorFormula.exists_bound_length_stalk_torSheaf_eq_zero X x

example : (Function.support fun p : ℕ ↦
    Module.length (X.presheaf.stalk x)
      ((TorFormula.torSheaf X F G p).presheaf.stalk x)).Finite :=
  TorFormula.finite_support_length_stalk_torSheaf X F G x

example : (Function.support fun p : ℕ ↦
    Stacks.Chow.sheafMultiplicity (TorFormula.torSheaf X F G p) x).Finite :=
  TorFormula.finite_support_sheafMultiplicity_torSheaf X F G x

example : (Function.support fun p : ℕ ↦
    (-1 : ℤ) ^ p * Stacks.Chow.sheafMultiplicity (TorFormula.torSheaf X F G p) x).Finite :=
  TorFormula.finite_support_signed_sheafMultiplicity_torSheaf X F G x

end
