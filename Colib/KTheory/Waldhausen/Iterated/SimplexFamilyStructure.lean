/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Waldhausen.Iterated.SimplexFamily
public import Colib.KTheory.Waldhausen.Iterated.StructureHomotopy
public import Colib.Topology.Realization.SimplexCylinder

/-!
# Structure compatibility of original iterated S-simplex families

The parameter simplex and the native suspension simplex use distinct coordinates.
The structure square leaves both of them unchanged.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor MonoidalCategory
open scoped Simplicial

universe u

namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory

namespace ModelSimplex

variable {V W T : WideSubcategory preservesZero.{u}} {k : ℕ}

/-- Precomposition retains all the original transformations. -/
def precomp (S : ModelSimplex V W k) (J : T ⟶ V) : ModelSimplex T W k where
  diagram := S.diagram ⋙ (whiskeringLeft T.obj.Obj V.obj.Obj W.obj.Obj).obj J.hom.toFunctor
  exact i := J.hom.isExact.comp (S.exact i)
  zero i := (congrArg (S.diagram.obj i).obj J.property).trans (S.zero i)
  weak i j f X := S.weak i j f (J.hom.toFunctor.obj X)

/-- Postcomposition retains all the original transformations. -/
def postcomp (S : ModelSimplex V W k) (J : W ⟶ T) : ModelSimplex V T k where
  diagram := S.diagram ⋙ (whiskeringRight V.obj.Obj W.obj.Obj T.obj.Obj).obj J.hom.toFunctor
  exact i := (S.exact i).comp J.hom.isExact
  zero i := (congrArg J.hom.toFunctor.obj (S.zero i)).trans J.property
  weak i j f X := J.hom.isExact.weak _ (S.weak i j f X)

/-- Exactness, zero and weakness witnesses are determined once the whole diagram agrees. -/
theorem ext_diagram {S T : ModelSimplex V W k} (h : S.diagram = T.diagram) : S = T := by
  cases S
  cases T
  cases h
  rfl

/-- Every edge of the finite diagram respects the original row insertion. -/
theorem insertion_square (S : ModelSimplex V W k) {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    S.postcomp ((insertion τ).app W) = (S.rows n).precomp ((insertion τ).app V) := by
  apply ext_diagram
  refine CategoryTheory.Functor.ext
    (fun i ↦ congrArg (fun f ↦ f.hom.toFunctor) ((insertion τ).naturality (S.vertex i))) ?_
  intro i j f
  have h := rowsTransformation_insertion_square (F := S.vertex i) (G := S.vertex j)
    (S.diagram.map f) τ
  apply (cancel_mono (eqToHom
    (congrArg (fun g ↦ g.hom.toFunctor) ((insertion τ).naturality (S.vertex j))))).1
  simpa only [postcomp, precomp, rows, vertex, Functor.comp_obj, Functor.comp_map,
    whiskeringLeft_obj_obj, whiskeringRight_obj_obj, whiskeringLeft_obj_map,
    whiskeringRight_obj_map,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using h

end ModelSimplex

/-- Whiskering the full original nerve simplex commutes with exact target evaluation. -/
theorem nerveSimplexDiagram_postcomp {C D : Type u} [Category C] [Category D]
    {n m : SimplexCategory} {k : ℕ} (K : Fin (k + 1) ⥤ (Grid₂ n m ⥤ C))
    (J : C ⥤ D) (τ : m ⟶ ⦋k⦌) :
    nerveSimplexDiagram (K ⋙ (whiskeringRight _ C D).obj J) τ =
      nerveSimplexDiagram K τ ⋙ J := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp [nerveSimplexDiagram, Functor.uncurry, Functor.map_comp]

/-- Evaluation is natural under an actual exact target functor. -/
theorem stageSimplexFunction_postcomp (r : ℕ)
    {V W T : WideSubcategory preservesZero.{u}} {k : ℕ}
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

/-- Evaluation is natural under an actual exact source functor. -/
theorem stageSimplexFunction_precomp (r : ℕ)
    {V W T : WideSubcategory preservesZero.{u}} {k : ℕ}
    (S : ModelSimplex V W k) (J : T ⟶ V) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj T).obj n) (τ : (Δ[k]).obj n) :
    stageSimplexFunction r (S.precomp J) n A τ =
      stageSimplexFunction r S n (((stages r).map J).app n A) τ := by
  induction r generalizing V W T with
  | zero => rfl
  | succ r ih =>
    exact ih (S.rows n.unop) ((IteratedS.rows n.unop).map J) A

/-- The actual higher family commutes with simplicial restriction of its stage input. -/
theorem stageSimplexFunction_naturality (r : ℕ) {V W : WideSubcategory preservesZero.{u}}
    {k : ℕ} (S : ModelSimplex V W k) {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (A : ((stages r).obj V).obj n) (τ : (Δ[k]).obj n) :
    ((stages r).obj W).map α (stageSimplexFunction r S n A τ) =
      stageSimplexFunction r S m (((stages r).obj V).map α A) ((Δ[k]).map α τ) := by
  induction r generalizing V W with
  | zero => rfl
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

/-- The genuine natural transformation on each whole finite parameter simplex. -/
def stageTransformationSimplex (r : ℕ) {V W : WideSubcategory preservesZero.{u}}
    {k : ℕ} (S : ModelSimplex V W k) : (stages r).obj V ⊗ Δ[k] ⟶ (stages r).obj W where
  app n := ↾fun z ↦ stageSimplexFunction r S n z.1 z.2
  naturality n m α := by
    ext z : 3
    exact (stageSimplexFunction_naturality r S α z.1 z.2).symm

/-- The original suspension simplex is not changed by the higher parameter. -/
@[colib_ref "quillen" "Quillen/Waldhausen/SConstruction/Iterated/SimplexFamily.lean:191-209"
  "adaptation" "The independent original suspension coordinate is preserved."]
theorem stageSimplexFunction_structure (r : ℕ) {V W : WideSubcategory preservesZero.{u}}
    {k : ℕ} (S : ModelSimplex V W k) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj V).obj n) (τ : (Δ[1]).obj n) (θ : (Δ[k]).obj n) :
    stageSimplexFunction (r + 1) S n ((stageCylinder r V).app n (A, τ)) θ =
      (stageCylinder r W).app n (stageSimplexFunction r S n A θ, τ) := by
  change stageSimplexFunction r (S.rows n.unop) n
    (((stages r).map ((insertion τ.down).app V)).app n A) θ = _
  rw [← stageSimplexFunction_precomp, ← ModelSimplex.insertion_square]
  exact stageSimplexFunction_postcomp r S ((insertion τ.down).app W) n A θ

/-- The full simplicial square, with both actual coordinates present. -/
theorem stageTransformationSimplex_structure (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} {k : ℕ} (S : ModelSimplex V W k) :
    stageCylinder r V ▷ Δ[k] ≫ stageTransformationSimplex (r + 1) S =
      simplicialSimplexCylinderSwap ((stages r).obj V) k ≫
        stageTransformationSimplex r S ▷ Δ[1] ≫ stageCylinder r W := by
  ext n z : 4
  exact stageSimplexFunction_structure r S n z.1.1 z.1.2 z.2

end CategoryTheory.Waldhausen.IteratedS
