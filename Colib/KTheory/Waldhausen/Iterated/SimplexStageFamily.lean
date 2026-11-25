/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.NerveSimplexFamily
public import Colib.KTheory.Waldhausen.Iterated.NaturalHomotopy
public import Colib.Topology.Realization.SimplexCylinder

/-!
# Actual higher transformation families in the iterated S-construction

Each original chain of weak transformations passes through the native quotient rows.
At every S-stage the entire simplex is realized with the actual product comparison.

Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/SimplexFamily.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, lines 29–161 and 210–213.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial Topology
universe u
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology

/-- A chain of exact original functors and weak transformations preserving the chosen zero. -/
structure ModelSimplex (V W : WideSubcategory preservesZero.{u}) (k : ℕ) where
  /-- The actual natural-transformation chain. -/
  diagram : Fin (k + 1) ⥤ (V.obj.Obj ⥤ W.obj.Obj)
  exact (i) : IsExact V.obj.waldhausen.cof V.obj.waldhausen.weq
    W.obj.waldhausen.cof W.obj.waldhausen.weq (diagram.obj i)
  zero (i) : (diagram.obj i).obj V.obj.waldhausen.zero = W.obj.waldhausen.zero
  weak (i j) (f : i ⟶ j) (X) : W.obj.waldhausen.weq ((diagram.map f).app X)

namespace ModelSimplex
variable {V W T : WideSubcategory preservesZero.{u}} {k : ℕ}

/-- A vertex is precisely an original exact model morphism. -/
def vertex (S : ModelSimplex V W k) (i : Fin (k + 1)) : V ⟶ W :=
  ⟨⟨S.diagram.obj i, S.exact i⟩, S.zero i⟩

/-- The whole transformation chain passes to the actual quotient rows. -/
def rows (S : ModelSimplex V W k) (n : SimplexCategory) :
    ModelSimplex ((IteratedS.rows n).obj V) ((IteratedS.rows n).obj W) k where
  diagram := {
    obj i := ((IteratedS.rows n).map (S.vertex i)).hom.toFunctor
    map {i j} f := rowsTransformation (F := S.vertex i) (G := S.vertex j)
      (S.diagram.map f) n
    map_id i := by
      apply NatTrans.ext
      funext A
      apply ObjectProperty.hom_ext
      ext p
      change (S.diagram.map (𝟙 i)).app (A.obj.obj p) = 𝟙 _
      simp only [Functor.map_id, NatTrans.id_app]
    map_comp f g := by
      apply NatTrans.ext
      funext A
      apply ObjectProperty.hom_ext
      ext p
      change (S.diagram.map (f ≫ g)).app (A.obj.obj p) =
        (S.diagram.map f).app (A.obj.obj p) ≫ (S.diagram.map g).app (A.obj.obj p)
      simp only [Functor.map_comp, NatTrans.comp_app] }
  exact i := ((IteratedS.rows n).map (S.vertex i)).hom.isExact
  zero i := ((IteratedS.rows n).map (S.vertex i)).property
  weak i j f := rowsTransformation_weak (F := S.vertex i) (G := S.vertex j)
    (S.diagram.map f) (S.weak i j f) n

/-- Precomposition retains every original transformation. -/
def precomp (S : ModelSimplex V W k) (J : T ⟶ V) : ModelSimplex T W k where
  diagram := S.diagram ⋙ (whiskeringLeft T.obj.Obj V.obj.Obj W.obj.Obj).obj J.hom.toFunctor
  exact i := J.hom.isExact.comp (S.exact i)
  zero i := (congrArg (S.diagram.obj i).obj J.property).trans (S.zero i)
  weak i j f X := S.weak i j f (J.hom.toFunctor.obj X)

/-- Postcomposition retains every original transformation. -/
def postcomp (S : ModelSimplex V W k) (J : W ⟶ T) : ModelSimplex V T k where
  diagram := S.diagram ⋙ (whiskeringRight V.obj.Obj W.obj.Obj T.obj.Obj).obj J.hom.toFunctor
  exact i := (S.exact i).comp J.hom.isExact
  zero i := (congrArg J.hom.toFunctor.obj (S.zero i)).trans J.property
  weak i j f X := J.hom.isExact.weak _ (S.weak i j f X)

end ModelSimplex

/-- The same genuine simplex family at each original iterated S-level. -/
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

/-- Postcomposition retains the whole higher nerve family. -/
theorem nerveSimplexDiagram_postcomp {C D : Type u} [Category C] [Category D]
    {n m : SimplexCategory} {k : ℕ} (K : Fin (k + 1) ⥤ (Grid₂ n m ⥤ C))
    (J : C ⥤ D) (τ : m ⟶ ⦋k⦌) :
    nerveSimplexDiagram (K ⋙ (whiskeringRight _ C D).obj J) τ =
      nerveSimplexDiagram K τ ⋙ J := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp [nerveSimplexDiagram, Functor.uncurry, Functor.map_comp]

/-- The whole iterated simplex is natural under an original exact target functor. -/
theorem stageSimplexFunction_postcomp (r : ℕ) {V W T : WideSubcategory preservesZero.{u}} {k : ℕ}
    (S : ModelSimplex V W k) (J : W ⟶ T) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj V).obj n) (τ : (Δ[k]).obj n) :
    stageSimplexFunction r (S.postcomp J) n A τ =
      ((stages r).map J).app n (stageSimplexFunction r S n A τ) := by
  induction r generalizing V W T with
  | zero =>
    apply Subtype.ext
    exact nerveSimplexDiagram_postcomp
      (S.diagram ⋙ (whiskeringLeft _ V.obj.Obj W.obj.Obj).obj A.val) J.hom.toFunctor τ.down
  | succ r ih =>
    exact ih (S.rows n.unop) ((IteratedS.rows n.unop).map J) A

/-- The whole iterated simplex is natural under an original exact source functor. -/
theorem stageSimplexFunction_precomp (r : ℕ) {V W T : WideSubcategory preservesZero.{u}} {k : ℕ}
    (S : ModelSimplex V W k) (J : T ⟶ V) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj T).obj n) (τ : (Δ[k]).obj n) :
    stageSimplexFunction r (S.precomp J) n A τ =
      stageSimplexFunction r S n (((stages r).map J).app n A) τ := by
  induction r generalizing V W T with
  | zero => rfl
  | succ r ih =>
    exact ih (S.rows n.unop) ((IteratedS.rows n.unop).map J) A

/-- Simplicial reindexing retains the full original higher transformation family. -/
theorem stageSimplexFunction_naturality (r : ℕ) {V W : WideSubcategory preservesZero.{u}} {k : ℕ}
    (S : ModelSimplex V W k) {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (A : ((stages r).obj V).obj n) (τ : (Δ[k]).obj n) :
    ((stages r).obj W).map α (stageSimplexFunction r S n A τ) =
      stageSimplexFunction r S m (((stages r).obj V).map α A) ((Δ[k]).map α τ) := by
  induction r generalizing V W with
  | zero =>
    have h := congrArg (fun f ↦ f (A, τ))
      ((weakNaturalTransformationSimplex V.obj.waldhausen W.obj.waldhausen
        S.diagram S.exact S.weak).naturality α)
    exact h.symm
  | succ r ih =>
    change ((stages r).obj ((rows m.unop).obj W)).map α
      (((stages r).map ((rowsReindex α.unop).app W)).app n
        (stageSimplexFunction r (S.rows n.unop) n A τ)) = _
    rw [← stageSimplexFunction_postcomp, ih]
    change stageSimplexFunction r ((S.rows m.unop).precomp ((rowsReindex α.unop).app V))
      m (((stages r).obj ((rows n.unop).obj V)).map α A) ((Δ[k]).map α τ) = _
    rw [stageSimplexFunction_precomp]
    congr 1
    exact ConcreteCategory.congr_hom
      (((stages r).map ((rowsReindex α.unop).app V)).naturality α) A

/-- The actual simplicial higher family at each original iterated stage. -/
def stageTransformationSimplex (r : ℕ) {V W : WideSubcategory preservesZero.{u}} {k : ℕ}
    (S : ModelSimplex V W k) : (stages r).obj V ⊗ Δ[k] ⟶ (stages r).obj W where
  app n := ↾fun z ↦ stageSimplexFunction r S n z.1 z.2
  naturality n m α := by
    ext z : 3
    exact (stageSimplexFunction_naturality r S α z.1 z.2).symm

/-- The genuine continuous higher family at each original stage. -/
def stageSimplexRealization (r : ℕ) {V W : WideSubcategory preservesZero.{u}} {k : ℕ}
    (S : ModelSimplex V W k) :
    C(stageSpace r V × |(Δ[k] : SSet.{u})|, stageSpace r W) :=
  realizationSimplexFamily (stageTransformationSimplex r S)

end CategoryTheory.Waldhausen.IteratedS
