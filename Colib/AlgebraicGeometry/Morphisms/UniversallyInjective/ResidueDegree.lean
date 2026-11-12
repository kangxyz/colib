/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteInjectivePushforward
public import Colib.Util.References
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Invertible

/-!
# Full radicial residue degrees over a field

The actual residueFieldMap of a finite universally injective morphism is a finite purely
inseparable field extension. The structural map to Spec k transports k's exponential
characteristic to the original target residue field. Consequently every full residue degree
is a power of that exponential characteristic, is one in characteristic zero, and is coprime
to every integer invertible in k. No separable-degree replacement is made.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Y) [IsFinite f] [UniversallyInjective f]
  (g : Y ⟶ Spec (.of k))

include g

/-- The full residue degree of a finite radicial morphism over k is a power of the
exponential characteristic of k, with the original residue-field map retained. -/
@[colib_tag "COL-1094", stacks 01S4 "radicial residue-field maps are purely inseparable",
  stacks 09HI "corollary: the full degree is a power of the positive characteristic",
  stacks 09HE "a purely inseparable extension in characteristic zero is trivial"]
theorem residueDegree_eq_pow_of_expChar (x : X) (p : ℕ) [ExpChar k p] :
    ∃ r : ℕ, f.residueDegree x = p ^ r := by
  let i : k →+* Y.residueField (f x) :=
    ((Spec.residueFieldIsoOfField (g (f x))).inv ≫ g.residueFieldMap (f x)).hom
  have : ExpChar (Y.residueField (f x)) p := expChar_of_injective_ringHom i.injective p
  let := (f.residueFieldMap x).hom.toAlgebra
  have : Module.Finite (Y.residueField (f x)) (X.residueField x) :=
    Module.finite_of_finrank_pos (f.residueDegree_pos_of_isFinite x)
  have hrad : UniversallyInjective f ↔ (Function.Injective f ∧
      ∀ y, (f.residueFieldMap y).hom.IsPurelyInseparable) :=
    (tfae_universallyInjective f).out 1 3
  have : IsPurelyInseparable (Y.residueField (f x)) (X.residueField x) :=
    (hrad.mp inferInstance).2 x
  exact IsPurelyInseparable.finrank_eq_pow (Y.residueField (f x)) (X.residueField x) p

/-- In characteristic zero the actual full residue degree of a finite radicial map is one. -/
theorem residueDegree_eq_one_of_charZero [CharZero k] (x : X) : f.residueDegree x = 1 := by
  obtain ⟨r, hr⟩ := residueDegree_eq_pow_of_expChar f g x 1
  simpa only [one_pow] using hr

/-- An integer invertible in the original field is coprime to every original finite
radicial residue degree, in characteristic zero as well as positive characteristic. -/
@[colib_tag "COL-1094"]
theorem residueDegree_coprime_of_isUnit (x : X) (n : ℕ) (hn : IsUnit (n : k)) :
    (f.residueDegree x).Coprime n := by
  obtain ⟨r, hr⟩ := residueDegree_eq_pow_of_expChar f g x (ringExpChar k)
  rw [hr]
  apply Nat.Coprime.pow_left
  rcases expChar_is_prime_or_one k (ringExpChar k) with hp | hp
  · have : CharP k (ringExpChar k) := (expChar_prime_iff k hp).mp inferInstance
    exact hp.coprime_iff_not_dvd.mpr ((CharP.isUnit_natCast_iff hp).mp hn)
  · rw [hp]
    exact Nat.coprime_one_left n

end AlgebraicGeometry.Scheme.Hom
