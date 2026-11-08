/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!
# Swapping two polynomial quotient factors and their actual branches

The whole mapped AdjoinRoot algebras are identified by the native tensor-product
commutativity equivalence. Both original algebra maps are retained on every
element. This exchanges all maximal ideals and induces the corresponding actual
quotient equivalences, without choosing a new branch carrier or residue field.

No field, irreducibility, separability, reducedness, or polynomial degree hypothesis
is needed. In particular, nilpotents are not discarded from the whole algebras.

This adapts the tensor comparison in `Aglib/RingTheory/AdjoinRootScalarBranches.lean`
and `AdjoinRootTensorBranches.lean` at revision
`52e09db47998f139064acf48a2d3a64494d0dd9a`. The coefficient maps are Mathlib's
existing `AdjoinRoot.map`, not separately defined maps.
-/

@[expose] public noncomputable section

open Polynomial
open scoped TensorProduct

namespace AdjoinRoot

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Scalar extension of the whole polynomial quotient, using the native tensor
and coefficient-equivalence constructions. -/
def scalarExtensionEquiv (p : R[X]) :
    S ⊗[R] AdjoinRoot p ≃ₐ[S] AdjoinRoot (p.map (algebraMap R S)) := by
  let e : S ⊗[R] R ≃ₐ[S] S := Algebra.TensorProduct.rid R S S
  exact (AdjoinRoot.tensorAlgEquiv p _ rfl).trans
    (AdjoinRoot.mapAlgEquiv e _ _ (by
      apply Associated.of_eq
      rw [Polynomial.map_map]
      congr 1
      apply RingHom.ext
      intro a
      change e (1 ⊗ₜ[R] a) = algebraMap R S a
      rw [Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one]))

/-- The original polynomial root remains the original root after base change. -/
@[simp]
theorem scalarExtensionEquiv_root (p : R[X]) :
    scalarExtensionEquiv (S := S) p (1 ⊗ₜ[R] root p) =
      root (p.map (algebraMap R S)) := by
  dsimp only [scalarExtensionEquiv]
  rw [AlgEquiv.trans_apply, tensorAlgEquiv_root, coe_mapAlgEquiv, map_root]

/-- The original coefficient inclusion is preserved by scalar extension. -/
@[simp]
theorem scalarExtensionEquiv_of (p : R[X]) (a : R) :
    scalarExtensionEquiv (S := S) p (1 ⊗ₜ[R] of p a) =
      of (p.map (algebraMap R S)) (algebraMap R S a) := by
  dsimp only [scalarExtensionEquiv]
  rw [AlgEquiv.trans_apply, tensorAlgEquiv_of, coe_mapAlgEquiv, map_of]
  change of _ ((Algebra.TensorProduct.rid R S S) (1 ⊗ₜ[R] a)) = _
  rw [Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one]

/-- On every element of the old algebra, the tensor comparison is the existing
AdjoinRoot coefficient map. -/
theorem scalarExtensionEquiv_comp_includeRight (p : R[X]) :
    (scalarExtensionEquiv (S := S) p).toRingHom.comp
        Algebra.TensorProduct.includeRight.toRingHom =
      AdjoinRoot.map (algebraMap R S) p (p.map (algebraMap R S)) dvd_rfl := by
  ext a <;> simp

variable (p h : R[X])

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "hE" => h.map (algebraMap R E)
local notation "pH" => p.map (algebraMap R H)

/-- Swap both original quotient factors in the whole unreduced algebra. -/
def tensorSwapEquiv : AdjoinRoot hE ≃ₐ[R] AdjoinRoot pH :=
  ((scalarExtensionEquiv (S := E) h).restrictScalars R).symm.trans
    ((Algebra.TensorProduct.comm R E H).trans
      ((scalarExtensionEquiv (S := H) p).restrictScalars R))

/-- The first original quotient algebra becomes the coefficient-extended old
root algebra on the other side. -/
theorem tensorSwapEquiv_algebraMap (a : E) :
    tensorSwapEquiv p h (algebraMap E (AdjoinRoot hE) a) =
      AdjoinRoot.map (algebraMap R H) p pH dvd_rfl a := by
  have ha : (scalarExtensionEquiv (S := E) h).symm
      (algebraMap E (AdjoinRoot hE) a) = a ⊗ₜ[R] (1 : H) := by
    apply (scalarExtensionEquiv (S := E) h).injective
    rw [AlgEquiv.apply_symm_apply]
    exact ((scalarExtensionEquiv (S := E) h).commutes a).symm
  change scalarExtensionEquiv (S := H) p
    (Algebra.TensorProduct.comm R E H
      ((scalarExtensionEquiv (S := E) h).symm
        (algebraMap E (AdjoinRoot hE) a))) = _
  rw [ha, Algebra.TensorProduct.comm_tmul]
  exact RingHom.congr_fun (scalarExtensionEquiv_comp_includeRight (S := H) p) a

/-- The second original quotient algebra becomes the literal coefficient
algebra on the other side. -/
theorem tensorSwapEquiv_map (b : H) :
    tensorSwapEquiv p h (AdjoinRoot.map (algebraMap R E) h hE dvd_rfl b) =
      algebraMap H (AdjoinRoot pH) b := by
  have hb : (scalarExtensionEquiv (S := E) h).symm
      (AdjoinRoot.map (algebraMap R E) h hE dvd_rfl b) = (1 : E) ⊗ₜ[R] b := by
    apply (scalarExtensionEquiv (S := E) h).injective
    rw [AlgEquiv.apply_symm_apply]
    exact (RingHom.congr_fun (scalarExtensionEquiv_comp_includeRight (S := E) h) b).symm
  change scalarExtensionEquiv (S := H) p
    (Algebra.TensorProduct.comm R E H
      ((scalarExtensionEquiv (S := E) h).symm
        (AdjoinRoot.map (algebraMap R E) h hE dvd_rfl b))) = _
  rw [hb, Algebra.TensorProduct.comm_tmul]
  exact (scalarExtensionEquiv (S := H) p).commutes b

/-- Tensor swapping matches every actual maximal ideal, without a factor-index
model and without reducing either whole algebra. -/
def tensorSwapMaximalEquiv :
    MaximalSpectrum (AdjoinRoot hE) ≃ MaximalSpectrum (AdjoinRoot pH) where
  toFun m := ⟨m.asIdeal.comap (tensorSwapEquiv p h).symm.toRingHom,
    m.isMaximal.comap_bijective _ (tensorSwapEquiv p h).symm.bijective⟩
  invFun m := ⟨m.asIdeal.comap (tensorSwapEquiv p h).toRingHom,
    m.isMaximal.comap_bijective _ (tensorSwapEquiv p h).bijective⟩
  left_inv m := by
    apply MaximalSpectrum.ext
    ext a
    change (tensorSwapEquiv p h).symm (tensorSwapEquiv p h a) ∈ m.asIdeal ↔ a ∈ m.asIdeal
    rw [AlgEquiv.symm_apply_apply]
  right_inv m := by
    apply MaximalSpectrum.ext
    ext a
    change tensorSwapEquiv p h ((tensorSwapEquiv p h).symm a) ∈ m.asIdeal ↔ a ∈ m.asIdeal
    rw [AlgEquiv.apply_symm_apply]

/-- The matched maximal ideal is the image under the actual whole-algebra map. -/
theorem tensorSwapMaximalEquiv_asIdeal (m : MaximalSpectrum (AdjoinRoot hE)) :
    (tensorSwapMaximalEquiv p h m).asIdeal = m.asIdeal.map (tensorSwapEquiv p h).toRingHom :=
  Ideal.comap_symm (tensorSwapEquiv p h).toRingEquiv

/-- The actual maximal quotients at matched branches are isomorphic. -/
def tensorSwapQuotientEquiv (m : MaximalSpectrum (AdjoinRoot hE)) :
    (AdjoinRoot hE ⧸ m.asIdeal) ≃+*
      (AdjoinRoot pH ⧸ (tensorSwapMaximalEquiv p h m).asIdeal) :=
  Ideal.quotientEquiv m.asIdeal (tensorSwapMaximalEquiv p h m).asIdeal
    (tensorSwapEquiv p h).toRingEquiv (tensorSwapMaximalEquiv_asIdeal p h m)

/-- The quotient comparison retains the whole tensor-swap square. -/
theorem tensorSwapQuotientEquiv_mk (m : MaximalSpectrum (AdjoinRoot hE))
    (x : AdjoinRoot hE) :
    tensorSwapQuotientEquiv p h m (Ideal.Quotient.mk m.asIdeal x) =
      Ideal.Quotient.mk (tensorSwapMaximalEquiv p h m).asIdeal (tensorSwapEquiv p h x) :=
  rfl

/-- The first original algebra map is retained after passage to the matched
actual maximal quotients. -/
theorem tensorSwapQuotientEquiv_algebraMap (m : MaximalSpectrum (AdjoinRoot hE)) (a : E) :
    tensorSwapQuotientEquiv p h m
        (Ideal.Quotient.mk m.asIdeal (algebraMap E (AdjoinRoot hE) a)) =
      Ideal.Quotient.mk (tensorSwapMaximalEquiv p h m).asIdeal
        (AdjoinRoot.map (algebraMap R H) p pH dvd_rfl a) := by
  rw [tensorSwapQuotientEquiv_mk, tensorSwapEquiv_algebraMap]

/-- The second original algebra map is retained after passage to the matched
actual maximal quotients. -/
theorem tensorSwapQuotientEquiv_map (m : MaximalSpectrum (AdjoinRoot hE)) (b : H) :
    tensorSwapQuotientEquiv p h m
        (Ideal.Quotient.mk m.asIdeal (AdjoinRoot.map (algebraMap R E) h hE dvd_rfl b)) =
      Ideal.Quotient.mk (tensorSwapMaximalEquiv p h m).asIdeal
        (algebraMap H (AdjoinRoot pH) b) := by
  rw [tensorSwapQuotientEquiv_mk, tensorSwapEquiv_map]

end AdjoinRoot
