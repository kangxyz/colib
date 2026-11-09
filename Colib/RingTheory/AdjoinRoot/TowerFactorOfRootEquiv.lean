/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.TowerFactor
public import Mathlib.FieldTheory.Minpoly.Field

/-!
# The actual tower factor determined by a root-preserving quotient equivalence

An actual `K`-algebra equivalence from a relative polynomial quotient to an
original top quotient induces the lower-to-top embedding by coefficient
restriction. If it preserves the original top root, the relative polynomial is
literally the native tower factor: both are its minimal polynomial under that
same coefficient action. Their quotient comparison is the original identity-
coefficient `AdjoinRoot.map`, not an abstract replacement of either field.

The lower and top polynomials need only be irreducible. The relative polynomial
is an existing monic irreducible point; its top divisibility is proved, not
assumed. There is no norm, presentation-independence, characteristic, normality,
separability, or complete nested-factor-index premise.

The proof uses the native tower-factor identities and minimal-polynomial API.
The complete-index construction can supply the equivalence downstream; this
module does not import it or assert its existence.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

namespace AdjoinRoot

local instance rootEquiv_nativeIrreducible {F : Type*} [Field F]
    {d : ℕ} (t : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly t)) :=
  ⟨irreducible t⟩

variable {K : Type*} [Field K] (r s : K[X])
  [Fact (Irreducible r)] [Fact (Irreducible s)]
  {n : ℕ} (t : MonicIrreducibleOfDegree (AdjoinRoot r) n)
  (ε : AdjoinRoot (poly t) ≃ₐ[K] AdjoinRoot s)

local notation "R" => AdjoinRoot r
local notation "T" => AdjoinRoot (poly t)
local notation "S" => AdjoinRoot s
local notation "i" => ε.toAlgHom.comp (ofAlgHom K (poly t))
local notation "q" => towerFactor r s i
local notation "U" => AdjoinRoot (poly q.1.2)
local notation "θ" => towerFactorRingEquiv r s i

/-- A root-preserving actual quotient equivalence identifies the literal tower polynomial. -/
theorem rootEquiv_poly_eq_towerFactor
    (hε : ε (root (poly t)) = root s) : poly t = poly q.1.2 := by
  let hRS : Algebra R S := (i).toRingHom.toAlgebra
  let eT : T →ₐ[R] S :=
    { ε.toRingHom with commutes' := fun a => rfl }
  let eU : U →ₐ[R] S :=
    { (θ).toRingHom with
      commutes' := fun a => towerFactorRingEquiv_algebraMap r s i a }
  have ht : aeval (root s) (poly t) = 0 := by
    have hz := AdjoinRoot.aeval_algHom_eq_zero (poly t) eT
    have hroot : eT (root (poly t)) = root s := hε
    rw [hroot] at hz
    exact hz
  have hq : aeval (root s) (poly q.1.2) = 0 := by
    have hz := AdjoinRoot.aeval_algHom_eq_zero (poly q.1.2) eU
    have hroot : eU (root (poly q.1.2)) = root s :=
      towerFactorRingEquiv_root r s i
    rw [hroot] at hz
    exact hz
  exact (minpoly.eq_of_irreducible_of_monic (irreducible t) ht (monic t)).trans
    (minpoly.eq_of_irreducible_of_monic (irreducible q.1.2) hq (monic q.1.2)).symm

/-- The canonical factor divides the literal identity-coefficient image of the relative factor. -/
theorem rootEquiv_towerFactor_dvd_map_id
    (hε : ε (root (poly t)) = root s) :
    poly q.1.2 ∣ (poly t).map (RingHom.id R) := by
  simpa only [Polynomial.map_id, rootEquiv_poly_eq_towerFactor r s t ε hε] using
    (dvd_refl (poly q.1.2))

/-- Compare the two actual relative quotients through their given maps to the top quotient. -/
def rootEquivTowerRingEquiv : T ≃+* U := ε.toRingEquiv.trans (θ).symm

/-- The actual quotient comparison fixes every original lower-field coefficient. -/
theorem rootEquivTowerRingEquiv_algebraMap (a : R) :
    rootEquivTowerRingEquiv r s t ε (algebraMap R T a) = algebraMap R U a := by
  apply (θ).injective
  change θ ((θ).symm (ε (algebraMap R T a))) = θ (algebraMap R U a)
  rw [RingEquiv.apply_symm_apply, towerFactorRingEquiv_algebraMap]
  rfl

/-- The original relative root maps to the actual canonical tower root. -/
theorem rootEquivTowerRingEquiv_root (hε : ε (root (poly t)) = root s) :
    rootEquivTowerRingEquiv r s t ε (root (poly t)) = root (poly q.1.2) := by
  apply (θ).injective
  change θ ((θ).symm (ε (root (poly t)))) = θ (root (poly q.1.2))
  rw [RingEquiv.apply_symm_apply, hε, towerFactorRingEquiv_root]

/-- The comparison is precisely the native quotient map with identity coefficients. -/
theorem rootEquivTowerRingEquiv_toRingHom (hε : ε (root (poly t)) = root s) :
    (rootEquivTowerRingEquiv r s t ε).toRingHom =
      AdjoinRoot.map (RingHom.id R) (poly t) (poly q.1.2)
        (rootEquiv_towerFactor_dvd_map_id r s t ε hε) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    change rootEquivTowerRingEquiv r s t ε (of (poly t) a) =
      AdjoinRoot.map (RingHom.id R) (poly t) (poly q.1.2)
        (rootEquiv_towerFactor_dvd_map_id r s t ε hε) (of (poly t) a)
    rw [AdjoinRoot.map_of]
    exact rootEquivTowerRingEquiv_algebraMap r s t ε a
  · change rootEquivTowerRingEquiv r s t ε (root (poly t)) =
      AdjoinRoot.map (RingHom.id R) (poly t) (poly q.1.2)
        (rootEquiv_towerFactor_dvd_map_id r s t ε hε) (root (poly t))
    rw [AdjoinRoot.map_root]
    exact rootEquivTowerRingEquiv_root r s t ε hε

/-- Composing the comparison with the canonical top map recovers the original equivalence. -/
theorem rootEquivTowerRingEquiv_comp_towerFactorRingEquiv :
    (θ).toRingHom.comp (rootEquivTowerRingEquiv r s t ε).toRingHom = ε.toRingHom := by
  apply RingHom.ext
  intro x
  change θ ((θ).symm (ε x)) = ε x
  exact (θ).apply_symm_apply (ε x)

end AdjoinRoot

end
