/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import StacksFrontier.AlgebraicTopology.AlexanderWhitneyDevissage
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# The Alexander–Whitney map in an abelian monoidal category

The pinned map is natural in both simplicial variables. Its degreewise
split décalage proof applies in an abelian monoidal category with additive
tensor, using the kernel of the zeroth face in that category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite SimplexCategory

open scoped Simplicial

namespace AlgebraicTopology

variable {C : Type*} [Category* C] [Abelian C]

section Naturality

variable [MonoidalCategory C] [MonoidalPreadditive C]

/-- The Alexander–Whitney comparison is natural in the two simplicial factors. -/
@[reassoc]
theorem alexanderWhitney_naturality {M N M' N' : SimplicialObject C}
    (f : M ⟶ M') (g : N ⟶ N') :
    alexanderWhitney M N ≫ HomologicalComplex.tensorHom
        ((alternatingFaceMapComplex C).map f) ((alternatingFaceMapComplex C).map g) =
      (alternatingFaceMapComplex C).map (f ⊗ₘ g) ≫ alexanderWhitney M' N' := by
  ext m : 1
  simp only [HomologicalComplex.comp_f, alternatingFaceMapComplex_map_f]
  change awApp M N m ≫ _ = (f.app (op ⦋m⦌) ⊗ₘ g.app (op ⦋m⦌)) ≫ awApp M' N' m
  rw [awApp, awApp, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have h : x.1 + x.2 = m := Finset.mem_antidiagonal.mp hx
  rw [awTerm_eq M N m x h (by omega) (by omega), awTerm_eq M' N' m x h (by omega) (by omega),
    Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [curriedTensor_map_app, curriedTensor_obj_map, alternatingFaceMapComplex_map_f,
    alternatingFaceMapComplex_obj_X, curriedTensor_obj_obj]
  rw [← tensorHom_def_assoc, ← Category.assoc, ← Category.assoc, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom, f.naturality (subinterval (n := m) 0 x.1 (by omega)).op,
    g.naturality (subinterval (n := m) x.1 x.2 (by omega)).op]

end Naturality

namespace AlexanderWhitney

open CategoryTheory.SimplicialObject

variable (N : SimplicialObject C)

private abbrev decalageKernel : SimplicialObject C := kernel (decδ₀ N)

private abbrev decalageShortComplex : ShortComplex (SimplicialObject C) :=
  ShortComplex.mk (kernel.ι (decδ₀ N)) (decδ₀ N) (kernel.condition _)

private abbrev sigmaZero (q : ℕ) : N _⦋q⦌ ⟶ (dec N) _⦋q⦌ :=
  N.σ (0 : Fin (q + 1))

omit [Abelian C] in
private theorem sigmaZero_comp_delta (q : ℕ) :
    sigmaZero N q ≫ (decδ₀ N).app (op ⦋q⦌) = 𝟙 _ :=
  N.δ_comp_σ_self' (by simp)

private abbrev projector (q : ℕ) : (dec N) _⦋q⦌ ⟶ (dec N) _⦋q⦌ :=
  𝟙 _ - (decδ₀ N).app (op ⦋q⦌) ≫ sigmaZero N q

private theorem projector_comp_delta (q : ℕ) :
    projector N q ≫ (decδ₀ N).app (op ⦋q⦌) = 0 := by
  simp only [projector, Preadditive.sub_comp, Category.id_comp, Category.assoc,
    sigmaZero_comp_delta, Category.comp_id, sub_self]

private def decalageKernelIso (q : ℕ) :
    (decalageKernel N).obj (op ⦋q⦌) ≅ kernel ((decδ₀ N).app (op ⦋q⦌)) :=
  PreservesKernel.iso ((CategoryTheory.evaluation SimplexCategoryᵒᵖ C).obj (op ⦋q⦌))
    (decδ₀ N)

@[reassoc]
private theorem decalageKernelIso_inv_ι (q : ℕ) :
    (decalageKernelIso N q).inv ≫ (kernel.ι (decδ₀ N)).app (op ⦋q⦌) =
      kernel.ι ((decδ₀ N).app (op ⦋q⦌)) :=
  PreservesKernel.iso_inv_ι _ _

private def retract (q : ℕ) : (dec N) _⦋q⦌ ⟶ (decalageKernel N).obj (op ⦋q⦌) :=
  kernel.lift _ (projector N q) (projector_comp_delta N q) ≫ (decalageKernelIso N q).inv

private theorem retract_comp_ι (q : ℕ) :
    retract N q ≫ (kernel.ι (decδ₀ N)).app (op ⦋q⦌) = projector N q := by
  rw [retract, Category.assoc, decalageKernelIso_inv_ι, kernel.lift_ι]

private theorem ι_comp_retract (q : ℕ) :
    (decalageShortComplex N).f.app (op ⦋q⦌) ≫ retract N q = 𝟙 _ := by
  let f := (kernel.ι (decδ₀ N)).app (op ⦋q⦌)
  let g := (decδ₀ N).app (op ⦋q⦌)
  let E := (CategoryTheory.evaluation SimplexCategoryᵒᵖ C).obj (op ⦋q⦌)
  let : Mono f := inferInstanceAs (Mono (E.map (kernel.ι (decδ₀ N))))
  apply (cancel_mono f).mp
  have h : f ≫ g = 0 :=
    congrArg (fun φ => φ.app (op ⦋q⦌)) (kernel.condition (decδ₀ N))
  change (f ≫ retract N q) ≫ f = 𝟙 _ ≫ f
  rw [Category.assoc, retract_comp_ι, Category.id_comp]
  simp only [projector, Preadditive.comp_sub, Category.comp_id, ← Category.assoc f]
  change f - (f ≫ g) ≫ sigmaZero N q = f
  rw [h, zero_comp, sub_zero]

private theorem splitting_identity (q : ℕ) :
    retract N q ≫ (decalageShortComplex N).f.app (op ⦋q⦌) +
      (decalageShortComplex N).g.app (op ⦋q⦌) ≫ sigmaZero N q = 𝟙 _ := by
  change retract N q ≫ (kernel.ι (decδ₀ N)).app (op ⦋q⦌) +
    (decδ₀ N).app (op ⦋q⦌) ≫ sigmaZero N q = 𝟙 _
  rw [retract_comp_ι, projector, sub_add_cancel]

end AlexanderWhitney

open AlexanderWhitney CategoryTheory.SimplicialObject

variable [MonoidalCategory C] [MonoidalPreadditive C]

/-- The pinned Alexander–Whitney map is a quasi-isomorphism in any abelian
monoidal category with additive tensor. -/
theorem quasiIso_alexanderWhitney (M N : SimplicialObject C) :
    QuasiIso (alexanderWhitney M N) := by
  have hepi : ∀ (n : ℕ) (V : SimplicialObject C),
      Epi (HomologicalComplex.homologyMap (alexanderWhitney M V) n) := by
    intro n
    induction n with
    | zero =>
      intro V
      exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ 0 (by simp)
    | succ n ih =>
      intro V
      exact epi_homologyMap_alexanderWhitney_of_splitting M (decalageShortComplex V)
        (retract V) (sigmaZero V) (ι_comp_retract V) (sigmaZero_comp_delta V)
        (splitting_identity V) (quasiIso_alexanderWhitney_dec M V) n (ih _)
  have hmono : ∀ (n : ℕ) (V : SimplicialObject C),
      Mono (HomologicalComplex.homologyMap (alexanderWhitney M V) n) := by
    intro n
    induction n with
    | zero =>
      intro V
      exact mono_homologyMap_alexanderWhitney_of_splitting M (decalageShortComplex V)
        (retract V) (sigmaZero V) (ι_comp_retract V) (sigmaZero_comp_delta V)
        (splitting_identity V) (quasiIso_alexanderWhitney_dec M V) 0 (hepi 0 _) (by simp)
    | succ n ih =>
      intro V
      refine mono_homologyMap_alexanderWhitney_of_splitting M (decalageShortComplex V)
        (retract V) (sigmaZero V) (ι_comp_retract V) (sigmaZero_comp_delta V)
        (splitting_identity V) (quasiIso_alexanderWhitney_dec M V) (n + 1) (hepi (n + 1) _)
        (fun j hj => ?_)
      obtain rfl : j = n := by simpa using hj
      exact ih _
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have := hepi n N
  have := hmono n N
  exact isIso_of_mono_of_epi _

end AlgebraicTopology
