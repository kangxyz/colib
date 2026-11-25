/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveStageFamily
public import Colib.KTheory.Waldhausen.Iterated.SimplexPrespectrum

/-!
# The realized reference stage family on actual characteristic simplices

The factorization uses the canonical finite-simplex product isomorphism and the original
realization map. In barycentric coordinates it is the entire native simplex family,
including its fixed value at the original point.

Adapted from `CommonReferenceNerve.lean` in Quillen K-theory at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor MonoidalCategory Convexity
open scoped Simplicial Topology
universe u

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
open SmallWaldhausenCategory SSet Topology

variable {V W : WideSubcategory preservesZero.{u}} (F₀ : V ⟶ W)

/-- Realize the nerve factorization through the unchanged finite-simplex product map. -/
def stageRealization (r : ℕ) {k : ℕ} (N : Fin (k + 1) → Node F₀) :
    C(stageSpace r V × |(Δ[k] : SSet.{u})|, stageSpace r W) :=
  (SSet.toTop.map (stageTransformation F₀ r)).hom.comp
    ((SSet.toTop.map ((stages r).obj V ◁ simplexMap F₀ N)).hom.comp
      (realizationProductSimplexIso ((stages r).obj V) k).inv.hom)

/-- The realized factorization is the same whole original finite-simplex map. -/
theorem stageRealization_eq (r : ℕ) {k : ℕ} (N : Fin (k + 1) → Node F₀) :
    stageRealization F₀ r N = stageSimplexRealization r
      (ModelSimplex.ofIsos F₀ (fun i ↦ (N i).1) (fun i ↦ (N i).2)) := by
  ext z
  change (SSet.toTop.map ((stages r).obj V ◁ simplexMap F₀ N) ≫
    SSet.toTop.map (stageTransformation F₀ r))
      ((realizationProductSimplexIso ((stages r).obj V) k).inv z) = _
  rw [← Functor.map_comp, stageTransformation_factorization]
  rfl

/-- Barycentric coordinates pass through the actual original realization homeomorphism. -/
def stageBarycentric (r : ℕ) {k : ℕ} (N : Fin (k + 1) → Node F₀) :
    C(StdSimplex ℝ (Fin (k + 1)) × stageSpace r V, stageSpace r W) :=
  ⟨fun z ↦ stageRealization F₀ r N (z.2, (SimplexCategory.toTopHomeo ⦋k⦌).symm z.1),
    by fun_prop⟩

/-- The full original barycentric family, without reparametrization. -/
theorem stageBarycentric_eq (r : ℕ) {k : ℕ} (N : Fin (k + 1) → Node F₀) :
    stageBarycentric F₀ r N = stageSimplexBarycentric
      (ModelSimplex.ofIsos F₀ (fun i ↦ (N i).1) (fun i ↦ (N i).2)) r := by
  ext z
  exact congrArg (fun f ↦ f (z.2, (SimplexCategory.toTopHomeo ⦋k⦌).symm z.1))
    (stageRealization_eq F₀ r N)

/-- The nerve factorization fixes the same original zero point for every parameter. -/
theorem stageBarycentric_point (r : ℕ) {k : ℕ} (N : Fin (k + 1) → Node F₀)
    (z : StdSimplex ℝ (Fin (k + 1))) :
    stageBarycentric F₀ r N (z, stagePoint r V) = stagePoint r W := by
  rw [stageBarycentric_eq]
  exact stageSimplexRealization_fixed_point r _ _

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
