/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Homology.ExtendScalars.Flat

/-!
# One-sided flat change of rings for actual categorical Tor

For a flat ring map `R → S`, an `R`-module `M`, and an arbitrary `S`-module `N`,
native categorical Tor of `N` and the base change of `M` over `S`, restricted
back to `R`, is Tor of the restricted `N` and `M` over `R`.

This follows by applying flat scalar extension to an actual projective
resolution of `M`, cancelling one ordinary tensor base change, and using the
exactness of scalar restriction to pass through homology. In particular, `N`
is not assumed to be extended from `R` or flat. This is the one-sided flat
change-of-rings step needed before native reduction to the full diagonal.

The tensor cancellation is Mathlib's `AlgebraTensorModule.cancelBaseChange`;
the homology comparison is the native exact-functor comparison. No replacement
Tor object or chosen-resolution hypothesis is introduced.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

namespace ModuleCat.Tor

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Tensoring an extended module with an actual `S`-module cancels the scalar extension. -/
def tensorExtensionRestrictionIso (N : ModuleCat.{u} S) :
    ModuleCat.extendScalars φ ⋙ tensorLeft N ⋙ ModuleCat.restrictScalars φ ≅
      tensorLeft ((ModuleCat.restrictScalars φ).obj N) := by
  let : Algebra R S := φ.toAlgebra
  let : Module R N := Module.compHom N φ
  let : IsScalarTower R S N := ⟨fun r s n => mul_smul (φ r) s n⟩
  refine NatIso.ofComponents (fun M =>
    LinearEquiv.toModuleIso
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S S N M).restrictScalars R)) ?_
  intro M M' f
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul n y =>
    induction y using TensorProduct.inductionOn with
    | tmul s m => rfl
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Flat extension carries projective resolutions to actual projective resolutions. -/
def flatExtendedProjectiveResolution (hφ : φ.Flat) {M : ModuleCat.{u} R}
    (P : ProjectiveResolution M) :
    ProjectiveResolution ((ModuleCat.extendScalars φ).obj M) := by
  have : (ModuleCat.restrictScalars φ).PreservesEpimorphisms :=
    ⟨fun {X Y} f hf => (ModuleCat.epi_iff_surjective _).mpr
      ((ModuleCat.epi_iff_surjective f).mp hf)⟩
  have : (ModuleCat.extendScalars φ).PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (ModuleCat.extendRestrictScalarsAdj φ)
  have : (ModuleCat.extendScalars φ).PreservesHomology :=
    extendScalars_preservesHomology_of_flat φ hφ
  exact (ModuleCat.extendScalars φ).mapProjectiveResolution P

/-- One-sided flat change of rings, with the actual ambient `R`-module structure retained. -/
def flatRestrictionIso (hφ : φ.Flat) (N : ModuleCat.{u} S) (M : ModuleCat.{u} R) (n : ℕ) :
    ((CategoryTheory.Tor (ModuleCat.{u} R) n).obj
      ((ModuleCat.restrictScalars φ).obj N)).obj M ≅
    (ModuleCat.restrictScalars φ).obj
      (((CategoryTheory.Tor (ModuleCat.{u} S) n).obj N).obj
        ((ModuleCat.extendScalars φ).obj M)) := by
  let P := projectiveResolution M
  let P' := flatExtendedProjectiveResolution φ hφ P
  exact P.isoLeftDerivedObj (tensorLeft ((ModuleCat.restrictScalars φ).obj N)) n ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.down ℕ) n).mapIso
      ((Functor.mapHomologicalComplexCompIso
        (tensorExtensionRestrictionIso φ N) (.down ℕ)).symm.app P.complex) ≪≫
    (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
      (ModuleCat.restrictScalars φ) (.down ℕ) n).app
        (((tensorLeft N).mapHomologicalComplex (.down ℕ)).obj P'.complex) ≪≫
    (ModuleCat.restrictScalars φ).mapIso (P'.isoLeftDerivedObj (tensorLeft N) n).symm

end ModuleCat.Tor
