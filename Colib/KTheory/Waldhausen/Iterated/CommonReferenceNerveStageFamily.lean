/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerve
public import Colib.KTheory.Waldhausen.Iterated.SimplexStageSpecifications

/-!
# The iterated Waldhausen stage family on the reference nerve

The full reference chains give the original simplicial family at every stage. Pullback
along any actual characteristic simplex recovers the corresponding native finite
family at every simplicial degree. No product inverse or compact continuity is used.

Adapted from `CommonReferenceNerve.lean` in Quillen K-theory at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial
universe u

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
open SmallWaldhausenCategory

variable {V W : WideSubcategory preservesZero.{u}} (F₀ : V ⟶ W)

/-- The actual simplicial family on all chains of the common-reference category. -/
def stageTransformation (r : ℕ) :
    (stages r).obj V ⊗ nerve (Codiscrete (Node F₀)) ⟶ (stages r).obj W where
  app n := ↾fun z ↦ stageSimplexFunction r (chain F₀ z.2) n z.1 ⟨𝟙 n.unop⟩
  naturality n m α := by
    ext z : 3
    symm
    change ((stages r).obj W).map α
        (stageSimplexFunction r (chain F₀ z.2) n z.1 ⟨𝟙 n.unop⟩) = _
    rw [stageSimplexFunction_naturality]
    change stageSimplexFunction r (chain F₀ z.2) m
        (((stages r).obj V).map α z.1) ⟨α.unop ≫ 𝟙 n.unop⟩ =
      stageSimplexFunction r
        (chain F₀ (α.unop.toOrderHom.monotone.functor ⋙ z.2)) m
        (((stages r).obj V).map α z.1) ⟨𝟙 m.unop⟩
    have h := stageSimplexFunction_face r (chain F₀ z.2) α.unop m
      (((stages r).obj V).map α z.1) ⟨𝟙 m.unop⟩
    simpa only [Category.id_comp, Category.comp_id, ← chain_face] using h

/-- The original finite simplex is exactly the restriction of the nerve family. -/
theorem stageTransformation_factorization (r : ℕ) {k : ℕ}
    (N : Fin (k + 1) → Node F₀) :
    (stages r).obj V ◁ simplexMap F₀ N ≫ stageTransformation F₀ r =
      stageTransformationSimplex r
        (ModelSimplex.ofIsos F₀ (fun i ↦ (N i).1) (fun i ↦ (N i).2)) := by
  ext n z : 4
  change stageSimplexFunction r (chain F₀ ((simplexMap F₀ N).app n z.2))
      n z.1 ⟨𝟙 n.unop⟩ =
    stageSimplexFunction r
      (ModelSimplex.ofIsos F₀ (fun i ↦ (N i).1) (fun i ↦ (N i).2)) n z.1 z.2
  have hc : chain F₀ ((simplexMap F₀ N).app n z.2) =
      (ModelSimplex.ofIsos F₀ (fun i ↦ (N i).1) (fun i ↦ (N i).2)).face z.2.down := by
    apply ModelSimplex.ext_diagram
    rfl
  rw [hc]
  have h := stageSimplexFunction_face r
    (ModelSimplex.ofIsos F₀ (fun i ↦ (N i).1) (fun i ↦ (N i).2))
    z.2.down n z.1 ⟨𝟙 n.unop⟩
  have he : (⟨𝟙 n.unop ≫ z.2.down⟩ : (Δ[k]).obj n) = z.2 := by
    apply ULift.ext
    exact Category.id_comp _
  rw [he] at h
  exact h.symm

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
