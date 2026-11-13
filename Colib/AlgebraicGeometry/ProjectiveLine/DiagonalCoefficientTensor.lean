/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Equalizer

/-! # Tensoring the diagonal sequence over the second factor

The algebraic step is that a short exact sequence of modules over an algebra,
with quotient flat over the base, remains exact after tensoring with a module
extended from the base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

section Algebra

variable {R A M N P E : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup E]
  [Module A M] [Module A N] [Module A P] [Module R E]
  [Module R M] [Module R N] [Module R P]
  [IsScalarTower R A M] [IsScalarTower R A N] [IsScalarTower R A P]

omit [Module A P] [Module R P] [IsScalarTower R A P] in
private theorem cancelBaseChange_map (f : M →ₗ[A] N) (x : M ⊗[A] (A ⊗[R] E)) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange R A A N E
        (f.rTensor (A ⊗[R] E) x) =
      (f.restrictScalars R).rTensor E
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A M E x) := by
  refine TensorProduct.inductionOn x ?_ ?_
  · intro m v
    refine TensorProduct.inductionOn v ?_ ?_
    · intro a e
      simp
    · intro x y hx hy
      simp only [TensorProduct.tmul_add, map_add, hx, hy]
  · intro x y hx hy
    simp [hx, hy]

/-- For a quotient flat over the base, tensoring with an extended module preserves the
inclusion, even if the quotient is not flat over the algebra. -/
theorem injective_rTensor_baseChange_of_flat_quotient
    (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) [Module.Flat R P] :
    Function.Injective (f.rTensor (A ⊗[R] E)) := by
  have hR : Function.Injective ((f.restrictScalars R).rTensor E) := by
    rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
    exact LinearMap.lTensor_injective_of_exact_of_flat
      (g.restrictScalars R) hg (f.restrictScalars R) hf hfg E
  intro x y hxy
  apply (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A M E).injective
  apply hR
  rw [← cancelBaseChange_map f x, ← cancelBaseChange_map f y, hxy]

end Algebra

section ModuleCat

open MonoidalCategory

variable {R A : Type*} [CommRing R] [CommRing A] (α : R →+* A)

/-- The categorical form of tensor exactness for a module extended from the base. -/
theorem shortExact_tensorRight_extendScalars
    (S : ShortComplex (ModuleCat A)) (hS : S.ShortExact)
    (E : ModuleCat R)
    (hflat : Module.Flat R ((ModuleCat.restrictScalars α).obj S.X₃)) :
    (S.map (tensorRight ((ModuleCat.extendScalars α).obj E))).ShortExact := by
  let : Algebra R A := α.toAlgebra
  let : Module R S.X₁ := Module.compHom _ α
  let : Module R S.X₂ := Module.compHom _ α
  let : Module R S.X₃ := Module.compHom _ α
  let : IsScalarTower R A S.X₁ := SMul.comp.isScalarTower α
  let : IsScalarTower R A S.X₂ := SMul.comp.isScalarTower α
  let : IsScalarTower R A S.X₃ := SMul.comp.isScalarTower α
  have : Module.Flat R S.X₃ := hflat
  have hf : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective S.f).mp hS.mono_f
  have hg : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective S.g).mp hS.epi_g
  have hfg : Function.Exact S.f.hom S.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  apply ModuleCat.shortComplex_shortExact
  · exact rTensor_exact (A ⊗[R] E) hfg hg
  · exact injective_rTensor_baseChange_of_flat_quotient S.f.hom S.g.hom hf hfg hg
  · exact LinearMap.rTensor_surjective (A ⊗[R] E) hg

end ModuleCat

end AlgebraicGeometry.Scheme
