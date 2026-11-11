module

import Colib.RingTheory.Henselian.FiniteAlgebraUnits

universe u v

variable (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
variable (B : Type v) [CommRing B] [Algebra R B] [Module.Finite R B]

-- Independent universes and arbitrary (not necessarily local or reduced) finite algebras.
example {n : ℕ} (hn : IsUnit (n : R)) (b : B) (hb : IsUnit b) :
    ∃ c : B, c ^ n = b :=
  StrictlyHenselianLocalRing.exists_pow_eq_of_isUnit_of_module_finite R B hn hb

-- The exponent one needs no extra hypothesis.
example : Function.Surjective (fun u : Bˣ => u ^ (1 : ℕ)) :=
  StrictlyHenselianLocalRing.surjective_pow_units_of_module_finite R B (by simp)

-- The exponent need not be prime.
example (h6 : IsUnit (6 : R)) : Function.Surjective (fun u : Bˣ => u ^ (6 : ℕ)) :=
  StrictlyHenselianLocalRing.surjective_pow_units_of_module_finite R B h6

-- The zero algebra is included; in particular no Nontrivial B instance is required.
example {n : ℕ} (hn : IsUnit (n : R)) :
    Function.Surjective (fun u : PUnit.{v + 1}ˣ => u ^ n) :=
  StrictlyHenselianLocalRing.surjective_pow_units_of_module_finite R PUnit.{v + 1} hn
