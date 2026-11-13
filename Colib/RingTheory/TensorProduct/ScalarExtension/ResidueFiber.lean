/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.FiniteExtension.CoprimeTensorField
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The complete scalar residue fiber

The actual fiber algebra is identified with the tensor of the original residue
field and the scalar extension. Coprime full degrees make this entire algebra a
field and force uniqueness of every point over the original mark.

Extracted from `CoprimeIntegral.lean` at motivic revision
`a6805c4a87cdfd7717dd7a94039246a167f15380`, before scheme integrality enters.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.TensorProduct

universe u

/-- The full scalar-extension fiber algebra, with its original residue-field
scalar structure, is the tensor product of the residue and extension fields. -/
def scalarResidueFiberEquiv
    (k R L : Type u) [Field k] [CommRing R] [Field L]
    [Algebra k R] [Algebra k L] (x : PrimeSpectrum R) :
    x.asIdeal.Fiber (R ⊗[k] L) ≃ₐ[x.asIdeal.ResidueField]
      (x.asIdeal.ResidueField ⊗[k] L) :=
  cancelBaseChange k R x.asIdeal.ResidueField x.asIdeal.ResidueField L

/-- Exactly one point lies above the original mark; the proof identifies the
entire preimage with the spectrum of the actual tensor fiber. -/
theorem existsUnique_prime_over_of_coprime_residueDegree
    (k R L : Type u) [Field k] [CommRing R] [Field L]
    [Algebra k R] [Algebra k L]
    (x : PrimeSpectrum R)
    (h : (Module.finrank k x.asIdeal.ResidueField).Coprime (Module.finrank k L)) :
    ∃! y : PrimeSpectrum (R ⊗[k] L),
      PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x := by
  let e := scalarResidueFiberEquiv k R L x
  have hf := isField_of_coprime_finrank_linearDisjoint k x.asIdeal.ResidueField L h
  let : Field (x.asIdeal.Fiber (R ⊗[k] L)) := (e.toMulEquiv.isField hf).toField
  let E := PrimeSpectrum.preimageEquivFiber R (R ⊗[k] L) x
  let z : PrimeSpectrum (x.asIdeal.Fiber (R ⊗[k] L)) := ⟨⊥, inferInstance⟩
  let y := E.symm z
  refine ⟨y.val, y.property, ?_⟩
  intro y' hy'
  exact congrArg Subtype.val (E.injective (Subsingleton.elim (E ⟨y', hy'⟩) (E y)))

end Algebra.TensorProduct
