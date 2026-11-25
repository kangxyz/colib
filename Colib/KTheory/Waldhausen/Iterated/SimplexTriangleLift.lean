/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/

module

public import Colib.KTheory.Waldhausen.Iterated.PrespectrumCompositionHomotopy
public import Colib.KTheory.Waldhausen.Iterated.SimplexPrespectrumFaceEvaluation

/-!
# Exact transformation triangles in the original prespectrum simplex family

The actual two-arrow simplex agrees with the existing relative transformation homotopy at
every prespectrum level, including its original loop evaluation at level zero. Two component
equations identify this same triangle in a simplex built from a common reference functor.

Adapted from the original Quillen files under
`Quillen/Waldhausen/SConstruction/Iterated` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`:
`SimplexFaces.lean:25-70,87-132`, `SimplexIsomorphism.lean:27-59`,
and `SimplexTriangleLift.lean:53-90`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory Convexity
open scoped Simplicial Topology unitInterval
universe u

namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology

namespace ModelSimplex

/-- The original two-arrow chain as a higher-family input. -/
def triangle {V W : WideSubcategory preservesZero.{u}} {F G H : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A)) :
    ModelSimplex V W 2 where
  diagram := ComposableArrows.mk₂ η θ
  exact i := by
    fin_cases i
    · exact F.hom.isExact
    · exact G.hom.isExact
    · exact H.hom.isExact
  zero i := by
    fin_cases i
    · exact F.property
    · exact G.property
    · exact H.property
  weak i j f A := by
    have hf := leOfHom f
    fin_cases i <;> fin_cases j
    · change W.obj.waldhausen.weq (𝟙 (F.hom.toFunctor.obj A))
      exact W.obj.waldhausen.weq.id_mem _
    · exact hη A
    · exact W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)
    · exact False.elim ((by decide : ¬ (1 : Fin 3) ≤ 0) hf)
    · change W.obj.waldhausen.weq (𝟙 (G.hom.toFunctor.obj A))
      exact W.obj.waldhausen.weq.id_mem _
    · exact hθ A
    · exact False.elim ((by decide : ¬ (2 : Fin 3) ≤ 0) hf)
    · exact False.elim ((by decide : ¬ (2 : Fin 3) ≤ 1) hf)
    · change W.obj.waldhausen.weq (𝟙 (H.hom.toFunctor.obj A))
      exact W.obj.waldhausen.weq.id_mem _

/-- Passing to actual quotient rows retains the entire original two-arrow chain. -/
theorem rows_triangle {V W : WideSubcategory preservesZero.{u}} {F G H : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))
    (n : SimplexCategory) :
    (triangle η θ hη hθ).rows n =
      triangle (rowsTransformation η n) (rowsTransformation θ n)
        (rowsTransformation_weak η hη n) (rowsTransformation_weak θ hθ n) := by
  apply ext_diagram
  refine ComposableArrows.ext₂
    (f := ((triangle η θ hη hθ).rows n).diagram)
    (g := (triangle (rowsTransformation η n) (rowsTransformation θ n)
      (rowsTransformation_weak η hη n) (rowsTransformation_weak θ hθ n)).diagram)
    rfl rfl rfl ?_ ?_ <;> simp <;> rfl

variable {V W : WideSubcategory preservesZero.{u}}

/-- A common original comparison functor gives an actual chain of all selected exact functors. -/
def ofIsos {k : ℕ} (F₀ : V ⟶ W) (F : Fin (k + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.hom.toFunctor ≅ (F i).hom.toFunctor) : ModelSimplex V W k where
  diagram := {
    obj i := (F i).hom.toFunctor
    map {i j} _ := (ρ i).inv ≫ (ρ j).hom
    map_id _ := by simp
    map_comp _ _ := by simp [Category.assoc] }
  exact i := (F i).hom.isExact
  zero i := (F i).property
  weak i j _ X := by
    change W.obj.waldhausen.weq (((ρ i).inv ≫ (ρ j).hom).app X)
    exact W.obj.waldhausen.weq_iso _ inferInstance

/-- Two original transformation equations identify an entire triangle face of the common simplex. -/
theorem ofIsos_face_triangle {k : ℕ} (F₀ : V ⟶ W) (F : Fin (k + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.hom.toFunctor ≅ (F i).hom.toFunctor) (α : ⦋2⦌ ⟶ ⦋k⦌)
    (η : (F (α.toOrderHom 0)).hom.toFunctor ⟶ (F (α.toOrderHom 1)).hom.toFunctor)
    (θ : (F (α.toOrderHom 1)).hom.toFunctor ⟶ (F (α.toOrderHom 2)).hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))
    (eη : (ρ (α.toOrderHom 0)).hom ≫ η = (ρ (α.toOrderHom 1)).hom)
    (eθ : (ρ (α.toOrderHom 1)).hom ≫ θ = (ρ (α.toOrderHom 2)).hom) :
    (ofIsos F₀ F ρ).face α = triangle η θ hη hθ := by
  apply ext_diagram
  refine ComposableArrows.ext₂
    (f := ((ofIsos F₀ F ρ).face α).diagram) (g := (triangle η θ hη hθ).diagram)
    rfl rfl rfl ?_ ?_
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change (ρ (α.toOrderHom 0)).inv ≫ (ρ (α.toOrderHom 1)).hom = η
    rw [← eη]
    simp
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change (ρ (α.toOrderHom 1)).inv ≫ (ρ (α.toOrderHom 2)).hom = θ
    rw [← eθ]
    simp

end ModelSimplex

private theorem mk₂_whiskerLeft_simplex {K C D : Type*} [Category* K] [Category* C] [Category* D]
    (J : K ⥤ C) {F G H : C ⥤ D} (η : F ⟶ G) (θ : G ⟶ H) :
    ComposableArrows.mk₂ (whiskerLeft J η) (whiskerLeft J θ) =
      ComposableArrows.mk₂ η θ ⋙ (whiskeringLeft K C D).obj J := by
  apply ComposableArrows.ext₂
    (f := ComposableArrows.mk₂ (whiskerLeft J η) (whiskerLeft J θ))
    (g := ComposableArrows.mk₂ η θ ⋙ (whiskeringLeft K C D).obj J) rfl rfl rfl <;> simp

namespace ModelSimplex

/-- Precomposition preserves the entire original two-arrow transformation triangle. -/
theorem triangle_precomp {V W T : WideSubcategory preservesZero.{u}} {F G H : V ⟶ W}
    (J : T ⟶ V) (η : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (hη : ∀ X, W.obj.waldhausen.weq (η.app X))
    (hθ : ∀ X, W.obj.waldhausen.weq (θ.app X)) :
    (triangle η θ hη hθ).precomp J =
      triangle (F := J ≫ F) (G := J ≫ G) (H := J ≫ H)
        (whiskerLeft J.hom.toFunctor η) (whiskerLeft J.hom.toFunctor θ)
        (fun X ↦ hη (J.hom.toFunctor.obj X)) (fun X ↦ hθ (J.hom.toFunctor.obj X)) := by
  apply ext_diagram
  exact (mk₂_whiskerLeft_simplex J.hom.toFunctor η θ).symm

end ModelSimplex

/-- The higher family contains every point of the original iterated triangle. -/
theorem stageSimplexFunction_triangle (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} {F G H : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))
    (n : SimplexCategoryᵒᵖ) (A : ((stages r).obj V).obj n) (τ : (Δ[2]).obj n) :
    stageSimplexFunction r (ModelSimplex.triangle η θ hη hθ) n A τ =
      stageTriangleFunction r η θ hη hθ n A τ := by
  induction r generalizing V W with
  | zero =>
    apply Subtype.ext
    change nerveSimplexDiagram
      (ComposableArrows.mk₂ η θ ⋙ (whiskeringLeft _ V.obj.Obj W.obj.Obj).obj A.val)
        τ.down = _
    rw [← mk₂_whiskerLeft_simplex]
    rfl
  | succ r ih =>
    change stageSimplexFunction r ((ModelSimplex.triangle η θ hη hθ).rows n.unop)
      n A τ = _
    rw [ModelSimplex.rows_triangle]
    exact ih (rowsTransformation η n.unop) (rowsTransformation θ n.unop)
      (rowsTransformation_weak η hη n.unop) (rowsTransformation_weak θ hθ n.unop) A

/-- The old simplex is retained as an equality of entire simplicial transformation families. -/
theorem stageTransformationSimplex_triangle (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} {F G H : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A)) :
    stageTransformationSimplex r (ModelSimplex.triangle η θ hη hθ) =
      stageTransformationTriangle r η θ hη hθ := by
  ext n z : 4
  exact stageSimplexFunction_triangle r η θ hη hθ n z.1 z.2

/-- All continuous values of the original triangle are retained by the higher family. -/
theorem stageSimplexRealization_triangle (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} {F G H : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A)) :
    stageSimplexRealization r (ModelSimplex.triangle η θ hη hθ) =
      stageTriangleRealization η θ hη hθ r := by
  unfold stageSimplexRealization stageTriangleRealization
  rw [stageTransformationSimplex_triangle]

variable {V W : WideSubcategory preservesZero.{u}} {k : ℕ}

/-- The old full composition triangle is the common simplex evaluated at its actual parameters.
This includes its degree-zero loop family; no time coordinate is collapsed. -/
theorem prespectrumSimplexFamily_triangle {F G H : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (ModelSimplex.triangle η θ hη hθ) n
      (TheoremB.compositionTriangleHomotopy (r, s), x) =
        (prespectrumTransformationCompositionHomotopy η θ hη hθ).level n (r, (s, x)) := by
  have hs (j : ℕ) (y : stageSpace j V) :
      stageSimplexBarycentric (ModelSimplex.triangle η θ hη hθ) j
        (TheoremB.compositionTriangleHomotopy (r, s), y) =
        stageTransformationCompositionHomotopy η θ hη hθ j (r, (s, y)) := by
    change stageSimplexRealization j (ModelSimplex.triangle η θ hη hθ)
      (y, (SimplexCategory.toTopHomeo ⦋2⦌).symm
        (TheoremB.compositionTriangleHomotopy (r, s))) = _
    exact DFunLike.congr_fun (stageSimplexRealization_triangle j η θ hη hθ) _
  cases n with
  | zero =>
    change Path (stagePoint 0 V) (stagePoint 0 V) at x
    apply Path.ext
    funext t
    exact hs 0 (x t)
  | succ n => exact hs n x

/-- Two actual component equations place an old whole relative composition in one common family. -/
theorem prespectrumSimplexFamily_ofIsos_triangle
    (F₀ : V ⟶ W) (F : Fin (k + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.hom.toFunctor ≅ (F i).hom.toFunctor) (α : ⦋2⦌ ⟶ ⦋k⦌)
    (η : (F (α.toOrderHom 0)).hom.toFunctor ⟶ (F (α.toOrderHom 1)).hom.toFunctor)
    (θ : (F (α.toOrderHom 1)).hom.toFunctor ⟶ (F (α.toOrderHom 2)).hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))
    (eη : (ρ (α.toOrderHom 0)).hom ≫ η = (ρ (α.toOrderHom 1)).hom)
    (eθ : (ρ (α.toOrderHom 1)).hom ≫ θ = (ρ (α.toOrderHom 2)).hom)
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    prespectrumSimplexFamily (ModelSimplex.ofIsos F₀ F ρ) n
      (StdSimplex.map α.toOrderHom (TheoremB.compositionTriangleHomotopy (r, s)), x) =
        (prespectrumTransformationCompositionHomotopy η θ hη hθ).level n (r, (s, x)) := by
  rw [prespectrumSimplexFamily_face,
    ModelSimplex.ofIsos_face_triangle F₀ F ρ α η θ hη hθ eη eθ]
  exact prespectrumSimplexFamily_triangle η θ hη hθ n r s x

end CategoryTheory.Waldhausen.IteratedS
