/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakNaturalTransformationTriangle

/-!
# Higher simplex families of weak S-construction transformations

Higher simplex families of the same original weak S-construction transformations.
This produces the categorical input for a tetrahedral coherence; no Bass cube is asserted.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial
universe u v
namespace CategoryTheory.Waldhausen

/-- The simplex parameter sees only the nerve coordinate. -/
def nerveSimplexTimeFunctor (n : SimplexCategory) {m : SimplexCategory} {k : ℕ}
    (τ : m ⟶ ⦋k⦌) : Grid₂ n m ⥤ Fin (k + 1) :=
  (show Monotone (fun p : Grid₂ n m ↦ τ.toOrderHom p.1) from
    fun _ _ h ↦ τ.toOrderHom.monotone h.1).functor

/-- Evaluate a whole chain of original grids at the selected nerve coordinate. -/
def nerveSimplexDiagram {D : Type u} [Category.{v} D] {n m : SimplexCategory} {k : ℕ}
    (K : Fin (k + 1) ⥤ (Grid₂ n m ⥤ D)) (τ : m ⟶ ⦋k⦌) : Grid₂ n m ⥤ D :=
  ((nerveSimplexTimeFunctor n τ).prod' (𝟭 (Grid₂ n m))) ⋙ Functor.uncurry.obj K

/-- At a fixed nerve coordinate all S-arrows remain those of one original grid. -/
theorem nerveSimplexDiagram_rowMap {D : Type u} [Category.{v} D]
    {n m : SimplexCategory} {k : ℕ} (K : Fin (k + 1) ⥤ (Grid₂ n m ⥤ D))
    (τ : m ⟶ ⦋k⦌) (t : Fin (m.len + 1))
    (i j p q : Fin (n.len + 1)) (hij : i ≤ j) (hpq : p ≤ q)
    (f : grid₂ t i j hij ⟶ grid₂ t p q hpq) :
    (nerveSimplexDiagram K τ).map f = (K.obj (τ.toOrderHom t)).map f := by
  change (K.map (𝟙 (τ.toOrderHom t))).app (grid₂ t i j hij) ≫
    (K.obj (τ.toOrderHom t)).map f = _
  rw [K.map_id]
  simp only [NatTrans.id_app, Category.id_comp]

/-- Every dimension is admissible using only exact rows and the actual weak components. -/
theorem nerveSimplexDiagram_isSimplex₂ {D : Type u} [Category.{v} D]
    (W : Structure D) {n m : SimplexCategory} {k : ℕ}
    (K : Fin (k + 1) ⥤ (Grid₂ n m ⥤ D))
    (hK : ∀ i, IsSimplex₂ W.cof W.weq (K.obj i))
    (hweak : ∀ i j (f : i ⟶ j) p, W.weq ((K.map f).app p))
    (τ : m ⟶ ⦋k⦌) : IsSimplex₂ W.cof W.weq (nerveSimplexDiagram K τ) where
  zero t i := (hK (τ.toOrderHom t)).zero t i
  cofibration t i j p hij hjp := by
    simp only [nerveSimplexDiagram_rowMap]
    exact (hK (τ.toOrderHom t)).cofibration t i j p hij hjp
  quotient t i j p hij hjp := by
    simp only [nerveSimplexDiagram_rowMap]
    exact (hK (τ.toOrderHom t)).quotient t i j p hij hjp
  weak s t i j hst hij :=
    W.weq.comp_mem _ _
      (hweak _ _ (homOfLE (τ.toOrderHom.monotone hst)) (grid₂ s i j hij))
      ((hK (τ.toOrderHom t)).weak s t i j hst hij)

/-- Grid reindexing preserves the entire higher simplex family. -/
theorem nerveSimplexDiagram_precomp {D : Type u} [Category.{v} D]
    {n m n' m' : SimplexCategory} {k : ℕ}
    (K : Fin (k + 1) ⥤ (Grid₂ n m ⥤ D)) (α : n' ⟶ n) (β : m' ⟶ m)
    (τ : m ⟶ ⦋k⦌) :
    nerveSimplexDiagram (K ⋙ (whiskeringLeft _ _ D).obj (gridMap₂ α β)) (β ≫ τ) =
      gridMap₂ α β ⋙ nerveSimplexDiagram K τ := rfl

/-- Every simplex face is the original subchain, without a replacement cylinder. -/
theorem nerveSimplexDiagram_face {D : Type u} [Category.{v} D]
    {n m : SimplexCategory} {k l : ℕ}
    (K : Fin (k + 1) ⥤ (Grid₂ n m ⥤ D)) (α : ⦋l⦌ ⟶ ⦋k⦌) (τ : m ⟶ ⦋l⦌) :
    nerveSimplexDiagram K (τ ≫ α) =
      nerveSimplexDiagram (α.toOrderHom.monotone.functor ⋙ K) τ := rfl

/-- The maintained original triangle is the two-dimensional instance of this family. -/
theorem nerveSimplexDiagram_triangle {D : Type u} [Category.{v} D]
    {n m : SimplexCategory} {A B C : Grid₂ n m ⥤ D}
    (η : A ⟶ B) (θ : B ⟶ C) (τ : m ⟶ ⦋2⦌) :
    nerveSimplexDiagram (ComposableArrows.mk₂ η θ) τ = nerveTriangleDiagram η θ τ := rfl

/-- Every original zero grid gives a constant higher simplex. -/
theorem nerveSimplexDiagram_eq_const_of_zero {D : Type u} [Category.{v} D]
    {n m : SimplexCategory} {k : ℕ} (K : Fin (k + 1) ⥤ (Grid₂ n m ⥤ D))
    (Z : D) (hZ : IsZero Z) (hz : ∀ i p, (K.obj i).obj p = Z) (τ : m ⟶ ⦋k⦌) :
    nerveSimplexDiagram K τ = (Functor.const (Grid₂ n m)).obj Z := by
  have hobj (p : Grid₂ n m) : (nerveSimplexDiagram K τ).obj p = Z := hz _ p
  refine CategoryTheory.Functor.ext hobj ?_
  intro p q f
  exact (hZ.of_iso (eqToIso (hobj q))).eq_of_tgt _ _

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {k : ℕ}
  (K : Fin (k + 1) ⥤ (C ⥤ D))
  (hK : ∀ i, IsExact V.cof V.weq W.cof W.weq (K.obj i))
  (hweak : ∀ i j (f : i ⟶ j) X, W.weq ((K.map f).app X))

/-- The actual original S-construction supports all dimensions of transformation chains. -/
def weakNaturalTransformationSimplex : sSet V.cof V.weq ⊗ Δ[k] ⟶ sSet W.cof W.weq where
  app n := ↾fun z ↦ (bisimplicialDiagonalIso W).hom.app n
    ⟨nerveSimplexDiagram (K ⋙ (whiskeringLeft _ C D).obj z.1.val) z.2.down,
    nerveSimplexDiagram_isSimplex₂ W _
      (fun i ↦ (((bisimplicialSSetMap V.cof V.weq (hK i)).app n).app n
        ((bisimplicialDiagonalIso V).inv.app n z.1)).property)
      (fun i j f p ↦ hweak i j f (z.1.val.obj p)) z.2.down⟩
  naturality n m α := by
    ext z
    apply Subtype.ext
    rfl

/-- All parameter faces of the simplicial family use the exact subchain. -/
theorem weakNaturalTransformationSimplex_face {l : ℕ} (α : ⦋l⦌ ⟶ ⦋k⦌) :
    ((𝟙 (sSet V.cof V.weq)) ⊗ₘ SSet.stdSimplex.map α) ≫
        weakNaturalTransformationSimplex V W K hK hweak =
      weakNaturalTransformationSimplex V W (α.toOrderHom.monotone.functor ⋙ K)
        (fun i ↦ hK (α.toOrderHom i))
        (fun _ _ f X ↦ hweak _ _ (α.toOrderHom.monotone.functor.map f) X) := rfl

/-- The entire original chosen-zero vertex remains fixed in every simplex dimension. -/
theorem weakNaturalTransformationSimplex_fixed_zero
    (hz : ∀ i, (K.obj i).obj V.zero = W.zero) :
    SSet.yonedaEquiv.symm (zeroSimplex V.cof V.weq V.zero V.isZero (op ⦋0⦌)) ▷ Δ[k] ≫
        weakNaturalTransformationSimplex V W K hK hweak =
      CartesianMonoidalCategory.fst Δ[0] Δ[k] ≫
        SSet.yonedaEquiv.symm (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) := by
  ext n z
  apply Subtype.ext
  exact nerveSimplexDiagram_eq_const_of_zero _ W.zero W.isZero (fun i _ ↦ hz i) z.2.down

end CategoryTheory.Waldhausen
