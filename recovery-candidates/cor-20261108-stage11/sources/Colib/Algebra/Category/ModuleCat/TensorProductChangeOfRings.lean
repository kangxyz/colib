/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Scalar extension and the actual tensor-product ring action

The scalar extension of an algebra's underlying module is its tensor-product
ring, restricted along the literal left inclusion. The comparison is the identity
on pure tensors and retains the full algebra, including nilpotents. Composing
this identification with native `ModuleCat.extendScalarsComp` is the module
comparison needed for affine pulled-support stalks.

Implementation provenance: `motivic_source_a6805c4`,
`Motivic/Aglib/Algebra/Category/ModuleCat/Tor/SupportModulesAlgebra.lean`,
`regularBaseEquiv` and `extendQuotientAlgebraIso`, generalized from quotient algebras
to arbitrary commutative algebras, and the consumers in `SupportModulesMiddle.lean`.
This general module lemma does
not introduce another realization of Tor or a scheme-coordinate model.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped TensorProduct

universe u

namespace ModuleCat

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R T]

/-- The regular target module restricted along the algebra map has its given scalar action. -/
def restrictScalarsRegularAlgebraEquiv [Algebra R S] :
    (restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) ≃ₗ[R] S where
  __ := AddEquiv.refl S
  map_smul' r s := by
    change algebraMap R S r * (show S from s) = r • (show S from s)
    exact (Algebra.smul_def r (show S from s)).symm

/-- Scalar extension has the actual tensor-product ring's left-inclusion action,
retaining the existing algebra structure on the target. -/
def extendScalarsAlgebraTensorProductIso [Algebra R S] :
    (extendScalars (algebraMap R S)).obj (ModuleCat.of R T) ≅
      (restrictScalars (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] T)).obj
        (ModuleCat.of (S ⊗[R] T) (S ⊗[R] T)) := by
  let e : (extendScalars (algebraMap R S)).obj (ModuleCat.of R T) ≃+
      (restrictScalars (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] T)).obj
        (ModuleCat.of (S ⊗[R] T) (S ⊗[R] T)) :=
    (TensorProduct.congr (restrictScalarsRegularAlgebraEquiv (R := R) (S := S))
      (LinearEquiv.refl R T)).toAddEquiv
  refine LinearEquiv.toModuleIso
    (X₁ := (extendScalars (algebraMap R S)).obj (ModuleCat.of R T))
    (X₂ := (restrictScalars
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] T)).obj
        (ModuleCat.of (S ⊗[R] T) (S ⊗[R] T)))
    { e with map_smul' := ?_ }
  intro s x
  change e (s • x) = s • e x
  induction x using TensorProduct.inductionOn with
  | tmul s' t =>
    change S at s'
    change T at t
    change (s * s') ⊗ₜ[R] t = (s ⊗ₜ[R] (1 : T)) * (s' ⊗ₜ[R] t)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- Extending the actual tensor-ring module again is extension along the composed map. -/
def extendScalarsTensorProductCompIso [Algebra R S]
    {V : Type u} [CommRing V] (g : S →+* V) :
    (extendScalars g).obj
      ((restrictScalars (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] T)).obj
        (ModuleCat.of (S ⊗[R] T) (S ⊗[R] T))) ≅
    (extendScalars (g.comp (algebraMap R S))).obj (ModuleCat.of R T) :=
  (extendScalars g).mapIso (extendScalarsAlgebraTensorProductIso (R := R) (S := S)
    (T := T)).symm ≪≫
    ((extendScalarsComp (algebraMap R S) g).app (ModuleCat.of R T)).symm

end ModuleCat
