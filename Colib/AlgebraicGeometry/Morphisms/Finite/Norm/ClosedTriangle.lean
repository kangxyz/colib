/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Norm.FittingIdeal
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Norms of equations of an actual closed triangle

The closed subscheme has the same global sections from both affine
presentations. The quotient comparison uses its original restriction
maps and the scalar action of the finite morphism.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Morphisms/Finite/Norm/AffineClosedTriangle.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {A B D : Scheme.{u}} [IsAffine A] [IsAffine B]
  (p : B ⟶ A) (iB : D ⟶ B) [IsClosedImmersion iB]
  (iA : D ⟶ A) [IsClosedImmersion iA] (h : iB ≫ p = iA)
  (b : Γ(B, ⊤)) (a : Γ(A, ⊤))
  (hb : iB.ker.ideal ⟨⊤, isAffineOpen_top B⟩ = Ideal.span {b})
  (ha : iA.ker.ideal ⟨⊤, isAffineOpen_top A⟩ = Ideal.span {a})

/-- The exact two equations present the same closed scheme over the target. -/
def affineClosedTriangleQuotientEquiv :
    let : Algebra Γ(A, ⊤) Γ(B, ⊤) := p.appTop.hom.toAlgebra
    (Γ(B, ⊤) ⧸ Ideal.span {b}) ≃ₐ[Γ(A, ⊤)] (Γ(A, ⊤) ⧸ Ideal.span {a}) := by
  let : Algebra Γ(A, ⊤) Γ(B, ⊤) := p.appTop.hom.toAlgebra
  let : Algebra Γ(A, ⊤) Γ(D, ⊤) := iA.appTop.hom.toAlgebra
  let fB : Γ(B, ⊤) →ₐ[Γ(A, ⊤)] Γ(D, ⊤) :=
    { iB.appTop.hom with
      commutes' := fun r ↦ by
        change (p.appTop ≫ iB.appTop) r = iA.appTop r
        rw [← Hom.comp_appTop, h] }
  let fA : Γ(A, ⊤) →ₐ[Γ(A, ⊤)] Γ(D, ⊤) :=
    { iA.appTop.hom with commutes' := fun _ ↦ rfl }
  have hfB : Function.Surjective fB := iB.app_surjective ⊤ (isAffineOpen_top B)
  have hfA : Function.Surjective fA := iA.app_surjective ⊤ (isAffineOpen_top A)
  have hkB : RingHom.ker fB.toRingHom = Ideal.span {b} :=
    (iB.ker_apply ⟨⊤, isAffineOpen_top B⟩).symm.trans hb
  have hkA : RingHom.ker fA.toRingHom = Ideal.span {a} :=
    (iA.ker_apply ⟨⊤, isAffineOpen_top A⟩).symm.trans ha
  exact ((Ideal.quotientEquivAlgOfEq Γ(A, ⊤) hkB.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hfB)).trans
    ((Ideal.quotientEquivAlgOfEq Γ(A, ⊤) hkA.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hfA)).symm

include h hb ha in
/-- The norm of the source equation generates the ideal of the target equation. -/
theorem span_norm_eq_of_affineClosedTriangle [IsFinite p] :
    let : Algebra Γ(A, ⊤) Γ(B, ⊤) := p.appTop.hom.toAlgebra
    ∀ [Module.Free Γ(A, ⊤) Γ(B, ⊤)],
      Ideal.span {Algebra.norm Γ(A, ⊤) b} = Ideal.span {a} := by
  dsimp only
  let : Algebra Γ(A, ⊤) Γ(B, ⊤) := p.appTop.hom.toAlgebra
  intro hfree
  let : Module.Free Γ(A, ⊤) Γ(B, ⊤) := hfree
  let : Module.Finite Γ(A, ⊤) Γ(B, ⊤) := p.finite_appTop
  exact Algebra.span_norm_eq_of_quotient_linearEquiv b a
    (affineClosedTriangleQuotientEquiv p iB iA h b a hb ha).toLinearEquiv

end AlgebraicGeometry.Scheme.Hom
