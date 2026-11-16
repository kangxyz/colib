/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.NerveSimplexFamily
public import Colib.KTheory.Waldhausen.Iterated.NaturalHomotopy

/-!
# Finite transformation chains on the original iterated S-construction

The simplex is data on the existing Waldhausen categories and exact maps. Evaluating it passes
the entire chain and its chosen zero through the actual native quotient rows.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped Simplicial

universe u

namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory

/-- A chain of native exact functors preserving the specified zero, with pointwise weak edges. -/
structure ModelSimplex (V W : WideSubcategory preservesZero.{u}) (k : ℕ) where
  /-- The original transformation diagram. -/
  diagram : Fin (k + 1) ⥤ (V.obj.Obj ⥤ W.obj.Obj)
  /-- Exactness of each node. -/
  exact (i) : IsExact V.obj.waldhausen.cof V.obj.waldhausen.weq
    W.obj.waldhausen.cof W.obj.waldhausen.weq (diagram.obj i)
  /-- Each node preserves the specified zero literally. -/
  zero (i) : (diagram.obj i).obj V.obj.waldhausen.zero = W.obj.waldhausen.zero
  /-- All edge components are weak equivalences. -/
  weak (i j) (f : i ⟶ j) (X) : W.obj.waldhausen.weq ((diagram.map f).app X)

namespace ModelSimplex

variable {V W : WideSubcategory preservesZero.{u}} {k l : ℕ}

/-- The vertex is the same exact map in the native wide subcategory. -/
def vertex (S : ModelSimplex V W k) (i : Fin (k + 1)) : V ⟶ W :=
  ⟨⟨S.diagram.obj i, S.exact i⟩, S.zero i⟩

/-- Apply the actual quotient-row functor to every vertex and every edge. -/
def rows (S : ModelSimplex V W k) (n : SimplexCategory) :
    ModelSimplex ((IteratedS.rows n).obj V) ((IteratedS.rows n).obj W) k where
  diagram :=
    { obj i := ((IteratedS.rows n).map (S.vertex i)).hom.toFunctor
      map {i j} f := rowsTransformation (F := S.vertex i) (G := S.vertex j)
        (S.diagram.map f) n
      map_id i := by
        apply NatTrans.ext
        funext A
        apply ObjectProperty.hom_ext
        ext p
        simp [rowsTransformation]
        rfl
      map_comp f g := by
        apply NatTrans.ext
        funext A
        apply ObjectProperty.hom_ext
        ext p
        simp [rowsTransformation]
        rfl }
  exact i := ((IteratedS.rows n).map (S.vertex i)).hom.isExact
  zero i := ((IteratedS.rows n).map (S.vertex i)).property
  weak i j f := rowsTransformation_weak (F := S.vertex i) (G := S.vertex j)
    (S.diagram.map f) (S.weak i j f) n

/-- Restrict the complete transformation data along its prescribed ordered face. -/
def face (S : ModelSimplex V W k) (α : ⦋l⦌ ⟶ ⦋k⦌) : ModelSimplex V W l where
  diagram := α.toOrderHom.monotone.functor ⋙ S.diagram
  exact i := S.exact (α.toOrderHom i)
  zero i := S.zero (α.toOrderHom i)
  weak _ _ f X := S.weak _ _ (α.toOrderHom.monotone.functor.map f) X

end ModelSimplex

/-- Evaluate the same higher chain on the actual simplex at every original iterated stage. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/SimplexFamily.lean:87-99"
  "adaptation" "Recursion on the original quotient rows retains the complete transformation chain."]
def stageSimplexFunction (r : ℕ) :
    {V W : WideSubcategory preservesZero.{u}} → {k : ℕ} → ModelSimplex V W k →
    (n : SimplexCategoryᵒᵖ) → ((stages r).obj V).obj n → (Δ[k]).obj n →
      ((stages r).obj W).obj n := by
  induction r with
  | zero =>
    intro V W k S n A τ
    exact (weakNaturalTransformationSimplex V.obj.waldhausen W.obj.waldhausen
      S.diagram S.exact S.weak).app n (A, τ)
  | succ r ih =>
    intro V W k S n A τ
    exact ih (S.rows n.unop) n A τ

/-- Every parameter face is evaluation of the whole original restricted chain. -/
theorem stageSimplexFunction_face (r : ℕ) {V W : WideSubcategory preservesZero.{u}}
    {k l : ℕ} (S : ModelSimplex V W k) (α : ⦋l⦌ ⟶ ⦋k⦌) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj V).obj n) (τ : (Δ[l]).obj n) :
    stageSimplexFunction r S n A ⟨τ.down ≫ α⟩ =
      stageSimplexFunction r (S.face α) n A τ := by
  induction r generalizing V W with
  | zero => rfl
  | succ r ih => exact ih (S.rows n.unop) A

/-- The chosen zero simplex is fixed at every original stage and every parameter. -/
theorem stageSimplexFunction_zeroSimplex (r : ℕ) {V W : WideSubcategory preservesZero.{u}}
    {k : ℕ} (S : ModelSimplex V W k) (n : SimplexCategoryᵒᵖ) (τ : (Δ[k]).obj n) :
    stageSimplexFunction r S n (stageZeroSimplex r V n) τ = stageZeroSimplex r W n := by
  induction r generalizing V W with
  | zero =>
    apply Subtype.ext
    exact nerveSimplexDiagram_eq_const_of_zero _ W.obj.waldhausen.zero W.obj.waldhausen.isZero
      (fun i _ ↦ S.zero i) τ.down
  | succ r ih =>
    rw [stageZeroSimplex_succ, stageZeroSimplex_succ]
    exact ih (S.rows n.unop)

end CategoryTheory.Waldhausen.IteratedS
