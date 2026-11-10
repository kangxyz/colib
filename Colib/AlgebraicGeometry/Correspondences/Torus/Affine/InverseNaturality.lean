/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.CycleNorm
public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.AmbientNaturality

/-!
# The produced inverse commutes with actual native ambient changes

The map on cycles is the genuine finite pushforward along the explicit
coordinate-preserving ambient isomorphism. Surjectivity of the produced divisor
proves admissibility of this pushforward. Both the inverse and the independently
constructed support norm commute with it. The coefficient ring stays fixed;
this does not assert arbitrary coefficient pullback or global descent.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Chow Polynomial.BoundaryOneRationalFunctions

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {S T : Scheme.{u}} {R : Type u} [CommRing R] [IsDomain R]
  [IsIntegrallyClosed R] [IsNoetherianRing R]

/-- The actual finite pushforward preserves the native correspondence subgroup. -/
theorem ambientChange_mem (f : Spec (.of R) ⟶ S) (g : Spec (.of R) ⟶ T)
    (c : finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S)) :
    finiteCyclePushforward (ambientChangeIso f g).hom c.val ∈
      finiteCorrespondences g (multiplicativeGroupBaseChange T ↘ T) := by
  obtain ⟨a, rfl⟩ := rationalDivisorHom_surjective f c
  change finiteCyclePushforward (ambientChangeIso f g).hom
    (rationalDivisor f a.toMul).val ∈ _
  rw [rationalDivisor_ambientChangeIso]
  exact (rationalDivisor g a.toMul).property

/-- The geometric finite pushforward, restricted to actual native correspondence groups. -/
def ambientChangeHom (f : Spec (.of R) ⟶ S) (g : Spec (.of R) ⟶ T) :
    finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S) →+
      finiteCorrespondences g (multiplicativeGroupBaseChange T ↘ T) where
  toFun c := ⟨finiteCyclePushforward (ambientChangeIso f g).hom c.val,
    ambientChange_mem f g c⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' c d := Subtype.ext (map_add _ c.val d.val)

/-- The actual rational divisor commutes with the genuine native ambient change. -/
@[simp] theorem ambientChangeHom_rationalDivisor (f : Spec (.of R) ⟶ S)
    (g : Spec (.of R) ⟶ T) (a : admissibleGroup R) :
    ambientChangeHom f g (rationalDivisor f a) = rationalDivisor g a :=
  Subtype.ext (rationalDivisor_ambientChangeIso f g a)

/-- Recovery of the literal normalized rational function is independent of the native ambient. -/
@[simp] theorem cycleRationalFunction_ambientChangeHom (f : Spec (.of R) ⟶ S)
    (g : Spec (.of R) ⟶ T)
    (c : finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S)) :
    cycleRationalFunction g (ambientChangeHom f g c) = cycleRationalFunction f c := by
  obtain ⟨a, rfl⟩ := rationalDivisorHom_surjective f c
  change cycleRationalFunction g (ambientChangeHom f g (rationalDivisor f a.toMul)) = _
  rw [ambientChangeHom_rationalDivisor]
  exact (cycleRationalFunction_rationalDivisorHom g a).trans
    (cycleRationalFunction_rationalDivisorHom f a).symm

/-- The actual support determinant norm is invariant under the coordinate-preserving change. -/
@[simp] theorem cycleNorm_ambientChangeHom (f : Spec (.of R) ⟶ S)
    (g : Spec (.of R) ⟶ T)
    (c : finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S)) :
    cycleNorm g (ambientChangeHom f g c) = cycleNorm f c := by
  rw [cycleNorm_eq_signedValue_comp, cycleNorm_eq_signedValue_comp,
    AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    cycleRationalFunction_ambientChangeHom]

end AlgebraicGeometry.NativeTorusPolynomial
