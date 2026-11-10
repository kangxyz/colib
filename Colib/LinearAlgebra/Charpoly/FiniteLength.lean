/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.Algebra.Module.FiniteLength.Determinant
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# Finite-length characteristic polynomials and scalar multiplication

The native finite-length characteristic polynomial is compared with the ordinary
characteristic polynomial over a field. Its exact-sequence law then proves the scalar
multiplication formula with the full length, without evaluating polynomials on an
infinite field.

The scalar induction is adapted from the proof of
`FiniteLengthEndomorphism.multiplication_det_eq_norm_pow_length` in the pinned
`StacksFrontier.Algebra.Module.FiniteLength.Determinant`. It uses the same actual
modules, residue fields and composition-series characteristic polynomial.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FiniteLengthEndomorphism

universe u v w

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Native finite-length characteristic polynomials agree under an actual
intertwining linear equivalence. -/
theorem charpoly_eq_of_linearEquiv {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (hM : IsFiniteLength R M) (hN : IsFiniteLength R N)
    (φ : Module.End R M) (ψ : Module.End R N) (e : M ≃ₗ[R] N)
    (hφ : e.toLinearMap.comp φ = ψ.comp e.toLinearMap) :
    charpoly R hM φ = charpoly R hN ψ := by
  let g : N →ₗ[R] PUnit.{1} := 0
  have hexact : Function.Exact e.toLinearMap g := by
    rw [LinearMap.exact_iff]
    simp [g]
  have hcomm : g.comp ψ = (0 : Module.End R PUnit.{1}).comp g := by
    ext x
  simpa using (charpoly_exact R M N PUnit.{1} hM hN IsFiniteLength.of_subsingleton φ ψ 0
    e.toLinearMap g e.injective hexact (fun _ ↦ ⟨0, Subsingleton.elim _ _⟩) hφ hcomm).symm

section Field

variable {k : Type u} [Field k] {M : Type v} [AddCommGroup M] [Module k M]
  [Module.Finite k M]

/-- Over a field the native finite-length characteristic polynomial is the
coefficientwise residue image of the original linear characteristic polynomial. -/
theorem charpoly_eq_map_charpoly (hM : IsFiniteLength k M) (f : Module.End k M) :
    charpoly k hM f = f.charpoly.map (IsLocalRing.residue k) := by
  let K := IsLocalRing.ResidueField k
  let e : k ≃ₐ[k] K := AlgEquiv.ofBijective (Algebra.ofId k K)
    ⟨(algebraMap k K).injective, IsLocalRing.residue_surjective⟩
  let E : M ≃ₗ[k] K ⊗[k] M :=
    (TensorProduct.lid k M).symm.trans (e.toLinearEquiv.rTensor M)
  have hE (m : M) : E m = (1 : K) ⊗ₜ[k] m := by
    change e 1 ⊗ₜ[k] m = (1 : K) ⊗ₜ[k] m
    rw [map_one]
  have hT : IsFiniteLength k (K ⊗[k] M) := E.isFiniteLength hM
  have hcomm : E.toLinearMap.comp f =
      ((f.baseChange K).restrictScalars k).comp E.toLinearMap := by
    ext m
    change E (f m) = (f.baseChange K) (E m)
    simp only [hE, LinearMap.baseChange_tmul]
  calc
    charpoly k hM f = charpoly k hT ((f.baseChange K).restrictScalars k) :=
      charpoly_eq_of_linearEquiv hM hT f _ E hcomm
    _ = (f.baseChange K).charpoly := charpoly_residue k (K ⊗[k] M) hT (f.baseChange K)
    _ = f.charpoly.map (IsLocalRing.residue k) := LinearMap.charpoly_baseChange f K

end Field

private theorem nonempty_linearEquiv_residueField_of_isSimpleModule_charpoly
    (S : Type*) [CommRing S] [IsLocalRing S] (M : Type*) [AddCommGroup M] [Module S M]
    [IsSimpleModule S M] : Nonempty (M ≃ₗ[S] IsLocalRing.ResidueField S) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule S M›
  rw [IsLocalRing.eq_maximalIdeal hI] at e
  exact ⟨e⟩

private theorem finiteLength_restrictScalars_charpoly
    (R : Type u) [CommRing R] [IsLocalRing R]
    (R' : Type v) [CommRing R'] [IsLocalRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')]
    [Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R')]
    (M : Type w) [AddCommGroup M] [Module R M] [Module R' M] [IsScalarTower R R' M]
    (hM : IsFiniteLength R' M) : IsFiniteLength R M :=
  Module.length_ne_top_iff.mp <| by
    rw [IsLocalRing.length_restrictScalars R R' M]
    exact WithTop.mul_ne_top (Module.length_ne_top_iff.mpr hM) (by
      rw [Module.length_eq_finrank]
      exact ENat.natCast_ne_top _)

private theorem multiplication_charpoly_eq_pow_length_restrict
    (R : Type u) [CommRing R] [IsLocalRing R]
    (R' : Type v) [CommRing R'] [IsLocalRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')]
    [Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R')]
    (M : Type w) [AddCommGroup M] [Module R' M]
    (hM : IsFiniteLength R' M) (u : R') :
    letI : Module R M := Module.compHom M (algebraMap R R')
    letI : IsScalarTower R R' M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    FiniteLengthEndomorphism.charpoly R (finiteLength_restrictScalars_charpoly R R' M hM)
        ((LinearMap.lsmul R' M u).restrictScalars R) =
      (Algebra.lmul (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R')
        (IsLocalRing.residue R' u)).charpoly ^
        (Module.length R' M).toNat := by
  let : Module R M := Module.compHom M (algebraMap R R')
  let : IsScalarTower R R' M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  induction hM with
  | @of_subsingleton M _ _ hsub =>
      let : Module R M := Module.compHom M (algebraMap R R')
      let : IsScalarTower R R' M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
      have hd := FiniteLengthEndomorphism.smallValues_subsingleton R
        (finiteLength_restrictScalars_charpoly R R' M .of_subsingleton)
        ((LinearMap.lsmul R' M u).restrictScalars R)
      have hpoly := congrArg FiniteLengthEndomorphism.Values.characteristicPolynomial hd
      simpa [FiniteLengthEndomorphism.charpoly, Module.length_eq_zero] using hpoly
  | @of_simple_quotient M _ _ N _ hN ih =>
      let : Module R M := Module.compHom M (algebraMap R R')
      let : IsScalarTower R R' M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
      let : Module R N := Module.compHom N (algebraMap R R')
      let : IsScalarTower R R' N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
      let Q := M ⧸ N
      let : Module R Q := Module.compHom Q (algebraMap R R')
      let : IsScalarTower R R' Q := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
      let φN : Module.End R N := ((LinearMap.lsmul R' N u).restrictScalars R)
      let φM : Module.End R M := ((LinearMap.lsmul R' M u).restrictScalars R)
      let φQ : Module.End R Q := ((LinearMap.lsmul R' Q u).restrictScalars R)
      have hQ' : IsFiniteLength R' Q :=
        isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
      have hpoly := FiniteLengthEndomorphism.charpoly_exact R N M Q
        (finiteLength_restrictScalars_charpoly R R' N hN)
        (finiteLength_restrictScalars_charpoly R R' M (.of_simple_quotient hN))
        (finiteLength_restrictScalars_charpoly R R' Q hQ') φN φM φQ
        (N.subtype.restrictScalars R) (N.mkQ.restrictScalars R)
        N.subtype_injective (LinearMap.exact_iff.mpr (by
          rw [LinearMap.ker_restrictScalars, LinearMap.range_restrictScalars]
          congr 1
          rw [N.ker_mkQ]
          exact (Submodule.range_subtype N).symm)) N.mkQ_surjective
        (by ext x; rfl) (by ext x; rfl)
      rw [hpoly, ih]
      let K := IsLocalRing.ResidueField R'
      obtain ⟨e⟩ := nonempty_linearEquiv_residueField_of_isSimpleModule_charpoly R' Q
      let : IsSimpleModule R' K := IsSimpleModule.congr e.symm
      let φK : Module.End (IsLocalRing.ResidueField R) K :=
        LinearMap.lsmul K K (IsLocalRing.residue R' u)
      have hK' : IsFiniteLength R' K := Module.length_ne_top_iff.mp <| by
        rw [Module.length_eq_one_iff.mpr (inferInstance : IsSimpleModule R' K)]
        simp
      have hK : IsFiniteLength R K := finiteLength_restrictScalars_charpoly R R' K hK'
      have hzero : IsFiniteLength R PUnit.{1} := .of_subsingleton
      have hcompare := FiniteLengthEndomorphism.charpoly_exact R Q K PUnit.{1}
        (finiteLength_restrictScalars_charpoly R R' Q hQ') hK hzero φQ
        (φK.restrictScalars R) 0 (e.restrictScalars R) 0 e.injective
        (LinearMap.exact_iff.mpr (by
          rw [LinearMap.ker_zero]
          exact (LinearMap.range_eq_top.mpr
            (show Function.Surjective (e.restrictScalars R) from e.surjective)).symm))
        (fun x => ⟨0, Subsingleton.elim _ x⟩)
        (by ext x; exact e.map_smul u x) (by rfl)
      have hpolyQ : FiniteLengthEndomorphism.charpoly R
          (finiteLength_restrictScalars_charpoly R R' Q hQ') φQ =
          (Algebra.lmul (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R')
            (IsLocalRing.residue R' u)).charpoly := by
        rw [FiniteLengthEndomorphism.charpoly_zero, mul_one] at hcompare
        rw [← hcompare, FiniteLengthEndomorphism.charpoly_residue]
        rfl
      rw [hpolyQ]
      rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.subtype_injective
        N.mkQ_surjective (LinearMap.exact_iff.mpr (by rw [N.ker_mkQ, Submodule.range_subtype]))]
      rw [Module.length_eq_one_iff.mpr (inferInstance : IsSimpleModule R' Q), ENat.toNat_add]
      all_goals simp [Module.length_ne_top_iff.mpr hN, pow_succ]

/-- The finite-length characteristic polynomial of scalar multiplication is the
characteristic polynomial on the actual residue field to the full module length. -/
theorem multiplication_charpoly_eq_pow_length
    (R : Type u) [CommRing R] [IsLocalRing R]
    (R' : Type v) [CommRing R'] [IsLocalRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')]
    [Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R')]
    (M' : Type w) [AddCommGroup M'] [Module R M'] [Module R' M'] [IsScalarTower R R' M']
    (hM' : IsFiniteLength R' M') (u : R') :
    let hM : IsFiniteLength R M' := Module.length_ne_top_iff.mp <| by
      rw [IsLocalRing.length_restrictScalars R R' M']
      exact WithTop.mul_ne_top (Module.length_ne_top_iff.mpr hM') (by
        rw [Module.length_eq_finrank]
        exact ENat.natCast_ne_top _)
    FiniteLengthEndomorphism.charpoly R hM
        ((LinearMap.lsmul R' M' u).restrictScalars R) =
      (Algebra.lmul (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R')
        (IsLocalRing.residue R' u)).charpoly ^
        (Module.length R' M').toNat
    := by
  have hmodule : (inferInstance : Module R M') = Module.compHom M' (algebraMap R R') := by
    apply Module.ext'
    intro r x
    exact (IsScalarTower.algebraMap_smul R' r x).symm
  cases hmodule
  exact multiplication_charpoly_eq_pow_length_restrict R R' M' hM' u

end FiniteLengthEndomorphism

end
