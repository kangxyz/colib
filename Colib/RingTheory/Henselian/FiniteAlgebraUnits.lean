/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictlyHenselianFiniteAlgebras
public import StacksFrontier.RingTheory.DiscreteValuationRing.StrictlyHenselianKummerUnits

/-!
# Power roots of units in finite algebras over strictly henselian local rings

Let `R` be strictly henselian local and `B` a module-finite commutative `R`-algebra.
For every natural number `n` invertible in `R`, the `n`-th power map on `Bˣ` is surjective.
No locality, reducedness, flatness, or nontriviality assumption is imposed on `B`.

The proof uses the native decomposition into finite henselian local factors and the algebraic
extension of their residue fields. In each factor, the simple residue root of `X ^ n - u`
lifts by Hensel's lemma. The product decomposition includes the empty product, so the zero
algebra is covered as well. Although the native local root theorem is housed in a discrete
valuation ring module, its unit-root statement has no valuation or domain hypothesis.
-/

@[expose] public section

universe u v

namespace StrictlyHenselianLocalRing

variable (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
variable (B : Type v) [CommRing B] [Algebra R B] [Module.Finite R B]

/-- Every unit of a module-finite algebra over a strictly henselian local ring has an `n`-th
root whenever `n` is invertible in the base. The algebra need not be local or nonzero. -/
@[colib_tag "COL-1204",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/EtaleCohomology/HenselianRings/FiniteAlgebras.lean:44-74"
    "ingredient" "Finite henselian local factor decomposition, allowing an empty product",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/EtaleCohomology/HenselianRings/StrictlyHenselianFiniteAlgebras.lean:72-83"
    "ingredient" "Strict henselianity of finite henselian local factors",
  colib_ref "axiom_stacks_5ed82d14"
    "RingTheory/DiscreteValuationRing/StrictlyHenselianKummerUnits.lean:85-94"
    "ingredient" "Unit roots in each strictly henselian local factor; no DVR hypothesis"]
theorem exists_pow_eq_of_isUnit_of_module_finite {n : ℕ} (hn : IsUnit (n : R))
    {b : B} (hb : IsUnit b) : ∃ c : B, c ^ n = b := by
  classical
  obtain ⟨ι, hι, A, hcomm, halg, hhen, hfinite, ⟨e⟩⟩ :=
    exists_algEquiv_pi_henselianLocalRing_of_module_finite R B
  let : Finite ι := hι
  let : ∀ i, CommRing (A i) := hcomm
  let : ∀ i, Algebra R (A i) := halg
  let : ∀ i, HenselianLocalRing (A i) := hhen
  let : ∀ i, Module.Finite R (A i) := hfinite
  have hroot (i : ι) : ∃ c : A i, c ^ n = e b i := by
    let : IsLocalHom (algebraMap R (A i)) :=
      isLocalHom_algebraMap_of_finite_local R (A i)
    let : StrictlyHenselianLocalRing (A i) :=
      strictlyHenselianLocalRing_of_module_finite R (A i)
    have hnA : IsUnit (n : A i) := by
      simpa only [map_natCast] using hn.map (algebraMap R (A i))
    exact Stacks.StrictlyHenselianKummer.exists_pow_eq_of_isUnit (A i) hnA
      ((hb.map e.toRingHom).map (Pi.evalRingHom A i))
  choose c hc using hroot
  refine ⟨e.symm c, e.injective ?_⟩
  rw [map_pow, e.apply_symm_apply]
  exact funext hc

/-- The power map on the units of an arbitrary finite algebra over a strictly henselian
local ring is surjective when its exponent is invertible in the base. -/
@[colib_tag "COL-1204"]
theorem surjective_pow_units_of_module_finite {n : ℕ} (hn : IsUnit (n : R)) :
    Function.Surjective (fun u : Bˣ => u ^ n) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  intro u
  obtain ⟨b, hb⟩ := exists_pow_eq_of_isUnit_of_module_finite R B hn u.isUnit
  have hbu : IsUnit b := (isUnit_pow_iff hn0).mp (by rw [hb]; exact u.isUnit)
  refine ⟨hbu.unit, Units.ext ?_⟩
  simpa only [Units.val_pow_eq_pow_val, IsUnit.unit_spec] using hb

end StrictlyHenselianLocalRing
