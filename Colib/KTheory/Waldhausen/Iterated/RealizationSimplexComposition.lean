/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.KTheory.Waldhausen.Iterated.SimplexProductDiagram
public import Colib.Topology.Realization.JointSimplexParameter

/-!
# Realization of independently parameterized simplex families

The actual grid parameter evaluates to composition of the two complete
prespectrum families, including their based loops at level zero. Adapted
from `Quillen/Waldhausen/SConstruction/Iterated/RealizationSimplexComposition.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor MonoidalCategory
open CartesianMonoidalCategory Convexity Topology
open scoped Simplicial Topology
universe u
namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceProduct
open SmallWaldhausenCategory SSet

variable {V W T : WideSubcategory preservesZero.{u}} {p q : ℕ}
variable (F₀ : V ⟶ W) (F : Fin (p + 1) → (V ⟶ W))
  (ρ : ∀ i, F₀.hom.toFunctor ≅ (F i).hom.toFunctor)
variable (G₀ : W ⟶ T) (G : Fin (q + 1) → (W ⟶ T))
  (σ : ∀ i, G₀.hom.toFunctor ≅ (G i).hom.toFunctor)

/-- The actual realization of the common grid family is literal composition of the two whole
original realized families, with their parameters independent. -/
theorem realization_comp (r : ℕ) (x : stageSpace r V)
    (z : |(Δ[p] : SSet.{u})|) (w : |(Δ[q] : SSet.{u})|) :
    stageSimplexRealization r (simplex F₀ F ρ G₀ G σ)
      (x, SSet.toTop.map (SimplexGrid.embedding p q)
        ((realizationProductSimplexIso Δ[p] q).inv (z, w))) =
      stageSimplexRealization r (ModelSimplex.ofIsos G₀ G σ)
        (stageSimplexRealization r (ModelSimplex.ofIsos F₀ F ρ) (x, z), w) := by
  let X := (stages r).obj V
  let Y := (stages r).obj W
  let S := stageTransformationSimplex r (ModelSimplex.ofIsos F₀ F ρ)
  let K := stageTransformationSimplex r (ModelSimplex.ofIsos G₀ G σ)
  let D := stageTransformationSimplex r (simplex F₀ F ρ G₀ G σ)
  let ξ := (realizationProductSimplexIso (X ⊗ Δ[p]) q).inv
    ((realizationProductSimplexIso X p).inv (x, z), w)
  have hS := ConcreteCategory.congr_hom (realizationProductSimplexIso_inv_whisker S q)
    ((realizationProductSimplexIso X p).inv (x, z), w)
  change SSet.toTop.map (S ▷ Δ[q]) ξ =
    (realizationProductSimplexIso Y q).inv
      (SSet.toTop.map S ((realizationProductSimplexIso X p).inv (x, z)), w) at hS
  change SSet.toTop.map D ((realizationProductSimplexIso X (SimplexGrid.dimension p q)).inv
    (x, SSet.toTop.map (SimplexGrid.embedding p q)
      ((realizationProductSimplexIso Δ[p] q).inv (z, w)))) =
    SSet.toTop.map K ((realizationProductSimplexIso Y q).inv
      (SSet.toTop.map S ((realizationProductSimplexIso X p).inv (x, z)), w))
  rw [← hS, ← realization_joint_parameter_apply X (SimplexGrid.embedding p q) x z w]
  change (SSet.toTop.map ((α_ X Δ[p] Δ[q]).hom ≫ X ◁ SimplexGrid.embedding p q) ≫
    SSet.toTop.map D) ξ =
    (SSet.toTop.map (S ▷ Δ[q]) ≫ SSet.toTop.map K) ξ
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun h ↦ SSet.toTop.map h ξ)
    ((Category.assoc _ _ _).trans (stage_transformation_comp F₀ F ρ G₀ G σ r))

/-- The exact barycentric product parameter reproduces the whole original stage composition. -/
theorem barycentric_comp (r : ℕ) (x : stageSpace r V)
    (z : StdSimplex ℝ (Fin (p + 1))) (w : StdSimplex ℝ (Fin (q + 1))) :
    stageSimplexBarycentric (simplex F₀ F ρ G₀ G σ) r
      (SimplexGrid.parameter.{u} p q (z, w), x) =
      stageSimplexBarycentric (ModelSimplex.ofIsos G₀ G σ) r
        (w, stageSimplexBarycentric (ModelSimplex.ofIsos F₀ F ρ) r (z, x)) := by
  change stageSimplexRealization r (simplex F₀ F ρ G₀ G σ)
    (x, (SimplexCategory.toTopHomeo ⦋SimplexGrid.dimension p q⦌).symm
      (SimplexGrid.parameter p q (z, w))) = _
  unfold SimplexGrid.parameter
  simp only [ContinuousMap.coe_mk, Homeomorph.symm_apply_apply]
  exact realization_comp F₀ F ρ G₀ G σ r x
    ((SimplexCategory.toTopHomeo ⦋p⦌).symm z)
    ((SimplexCategory.toTopHomeo ⦋q⦌).symm w)

/-- Composition of both independently varying whole families at every original prespectrum level,
including the original loop input at level zero. -/
theorem prespectrum_comp (n : ℕ) (x : (prespectrum V).space n)
    (z : StdSimplex ℝ (Fin (p + 1))) (w : StdSimplex ℝ (Fin (q + 1))) :
    prespectrumSimplexFamily (simplex F₀ F ρ G₀ G σ) n
      (SimplexGrid.parameter.{u} p q (z, w), x) =
      prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ G σ) n
        (w, prespectrumSimplexFamily (ModelSimplex.ofIsos F₀ F ρ) n (z, x)) := by
  cases n with
  | zero =>
    change Path (stagePoint 0 V) (stagePoint 0 V) at x
    apply Path.ext
    funext t
    exact barycentric_comp F₀ F ρ G₀ G σ 0 (x t) z w
  | succ n => exact barycentric_comp F₀ F ρ G₀ G σ n x z w

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceProduct
