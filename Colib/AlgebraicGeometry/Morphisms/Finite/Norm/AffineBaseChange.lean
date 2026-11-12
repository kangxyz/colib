/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.AffinePullbackSections
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.RingTheory.Norm.BaseChangeProduct

/-!
# Base change of the actual finite free norm on affine charts

The determinant base-change theorem uses the original scalar maps, given
by pullback on global sections in the displayed Cartesian square.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme

/-- The determinant norm of the actual affine morphism commutes with base change
on the original sections. -/
theorem affineNorm_appTop_of_isPullback {W T Z P : Scheme.{u}} [IsAffine W] [IsAffine Z]
    (f : T ⟶ W) [IsFinite f] (g : Z ⟶ W)
    (a : P ⟶ T) (b : P ⟶ Z) (h : IsPullback a b f g) (s : Γ(T, ⊤)) :
    letI : Algebra Γ(W, ⊤) Γ(T, ⊤) := f.appTop.hom.toAlgebra
    letI : Algebra Γ(Z, ⊤) Γ(P, ⊤) := b.appTop.hom.toAlgebra
    ∀ [Module.Free Γ(W, ⊤) Γ(T, ⊤)],
      g.appTop (Algebra.norm Γ(W, ⊤) s) = Algebra.norm Γ(Z, ⊤) (a.appTop s) := by
  dsimp only
  let : IsAffine T := isAffine_of_isAffineHom f
  let : Algebra Γ(W, ⊤) Γ(T, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(W, ⊤) Γ(Z, ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(Z, ⊤) Γ(P, ⊤) := b.appTop.hom.toAlgebra
  intro hfree
  let : Module.Free Γ(W, ⊤) Γ(T, ⊤) := hfree
  let : Module.Finite Γ(W, ⊤) Γ(T, ⊤) := f.finite_appTop
  let e := affineSectionsComparisonOfIsPullback h
  rw [← e.2 s, Algebra.norm_eq_of_algEquiv]
  exact (Stacks.Norm.norm_tmul_one s).symm

end AlgebraicGeometry.Scheme
