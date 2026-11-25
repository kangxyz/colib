/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/

module

public import Colib.KTheory.Waldhausen.Iterated.SimplexStageFamily
public import Colib.KTheory.Waldhausen.Iterated.StructureHomotopy

/-!
# Face, chosen-zero and suspension equations for iterated S-simplex families

The original quotient-row insertion square controls every transformation in a chain.
It carries the independent suspension coordinate through realization, without changing
the actual simplex parameter or chosen stage zero.

Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/SimplexFamily.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, lines 163–208, 215–223, and 225–298.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial Topology unitInterval
universe u

namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology

namespace ModelSimplex

/-- Proof fields add no extra coherence to a fixed original chain. -/
theorem ext_diagram {V W : WideSubcategory preservesZero.{u}} {k : ℕ}
    {S T : ModelSimplex V W k}
    (h : S.diagram = T.diagram) : S = T := by
  cases S
  cases T
  cases h
  rfl

/-- All transformation components obey the original row-insertion square at once. -/
theorem insertion_square {V W : WideSubcategory preservesZero.{u}} {k : ℕ}
    (S : ModelSimplex V W k) {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    S.postcomp ((insertion τ).app W) = (S.rows n).precomp ((insertion τ).app V) := by
  apply ext_diagram
  refine CategoryTheory.Functor.ext
    (fun i ↦ congrArg (fun f ↦ f.hom.toFunctor) ((insertion τ).naturality (S.vertex i))) ?_
  intro i j f
  have h := rowsTransformation_insertion_square (F := S.vertex i) (G := S.vertex j)
    (S.diagram.map f) τ
  apply (cancel_mono (eqToHom
    (congrArg (fun f ↦ f.hom.toFunctor) ((insertion τ).naturality (S.vertex j))))).1
  simpa only [postcomp, precomp, rows, vertex, Functor.comp_obj, Functor.comp_map,
    whiskeringLeft_obj_obj, whiskeringRight_obj_obj,
    whiskeringLeft_obj_map, whiskeringRight_obj_map,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using h
end ModelSimplex

/-- Every higher simplex retains a separate original suspension coordinate. -/
theorem stageSimplexFunction_structure (r : ℕ) {V W : WideSubcategory preservesZero.{u}} {k : ℕ}
    (S : ModelSimplex V W k) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj V).obj n) (τ : (Δ[1]).obj n) (theta : (Δ[k]).obj n) :
    stageSimplexFunction (r + 1) S n ((stageCylinder r V).app n (A, τ)) theta =
      (stageCylinder r W).app n (stageSimplexFunction r S n A theta, τ) := by
  change stageSimplexFunction r (S.rows n.unop) n
    (((stages r).map ((insertion τ.down).app V)).app n A) theta = _
  rw [← stageSimplexFunction_precomp, ← ModelSimplex.insertion_square]
  exact stageSimplexFunction_postcomp r S ((insertion τ.down).app W) n A theta

/-- The complete mixed-coordinate simplicial square preserves the higher original simplex. -/
theorem stageTransformationSimplex_structure (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} {k : ℕ}
    (S : ModelSimplex V W k) :
    stageCylinder r V ▷ Δ[k] ≫ stageTransformationSimplex (r + 1) S =
      simplicialSimplexCylinderSwap ((stages r).obj V) k ≫
        stageTransformationSimplex r S ▷ Δ[1] ≫ stageCylinder r W := by
  ext n z : 4
  exact stageSimplexFunction_structure r S n z.1.1 z.1.2 z.2

/-- The realized higher simplex keeps its whole parameter independent from structure time. -/
theorem stageSimplexRealization_structure (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} {k : ℕ}
    (S : ModelSimplex V W k) (z : |(Δ[k] : SSet.{u})|) (t : unitInterval)
    (x : stageSpace r V) :
    stageSimplexRealization (r + 1) S (stageLoopMap r V x t, z) =
      stageLoopMap r W (stageSimplexRealization r S (x, z)) t :=
  realizationSimplexFamily_interchange (stageTransformationSimplex r S)
    (stageTransformationSimplex (r + 1) S) (stageHomotopy r V) (stageHomotopy r W)
    (stageTransformationSimplex_structure r S) z t x

namespace ModelSimplex

/-- The actual subchain selected by any simplex face or degeneracy. -/
def face {V W : WideSubcategory preservesZero.{u}} {k l : ℕ} (S : ModelSimplex V W k)
    (α : ⦋l⦌ ⟶ ⦋k⦌) : ModelSimplex V W l where
  diagram := α.toOrderHom.monotone.functor ⋙ S.diagram
  exact i := S.exact (α.toOrderHom i)
  zero i := S.zero (α.toOrderHom i)
  weak _i _j f X := S.weak _ _ (α.toOrderHom.monotone.functor.map f) X
end ModelSimplex

/-- Every iterated simplex face is the full original iterated family of its subchain. -/
theorem stageSimplexFunction_face (r : ℕ) {V W : WideSubcategory preservesZero.{u}} {k l : ℕ}
    (S : ModelSimplex V W k) (α : ⦋l⦌ ⟶ ⦋k⦌) (n : SimplexCategoryᵒᵖ)
    (A : ((stages r).obj V).obj n) (τ : (Δ[l]).obj n) :
    stageSimplexFunction r S n A ⟨τ.down ≫ α⟩ =
      stageSimplexFunction r (S.face α) n A τ := by
  induction r generalizing V W with
  | zero => rfl
  | succ r ih => exact ih (S.rows n.unop) A

/-- The simplicial face equations retain every point of the original subchain family. -/
theorem stageTransformationSimplex_face (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} {k l : ℕ}
    (S : ModelSimplex V W k) (α : ⦋l⦌ ⟶ ⦋k⦌) :
    ((𝟙 ((stages r).obj V)) ⊗ₘ SSet.stdSimplex.map α) ≫ stageTransformationSimplex r S =
      stageTransformationSimplex r (S.face α) := by
  ext n z : 4
  exact stageSimplexFunction_face r S α n z.1 z.2

/-- Every original zero simplex is fixed throughout the higher family. -/
theorem stageSimplexFunction_zeroSimplex (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} {k : ℕ}
    (S : ModelSimplex V W k) (n : SimplexCategoryᵒᵖ) (τ : (Δ[k]).obj n) :
    stageSimplexFunction r S n (stageZeroSimplex r V n) τ = stageZeroSimplex r W n := by
  induction r generalizing V W with
  | zero =>
    apply Subtype.ext
    exact nerveSimplexDiagram_eq_const_of_zero _ W.obj.waldhausen.zero W.obj.waldhausen.isZero
      (fun i _ ↦ S.zero i) τ.down
  | succ r ih =>
    rw [stageZeroSimplex_succ, stageZeroSimplex_succ]
    exact ih (S.rows n.unop)

/-- The complete original higher simplex is constant along the original chosen-zero vertex. -/
theorem stageTransformationSimplex_fixed_vertex (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} {k : ℕ}
    (S : ModelSimplex V W k) :
    SSet.yonedaEquiv.symm (stageVertex r V) ▷ Δ[k] ≫ stageTransformationSimplex r S =
      CartesianMonoidalCategory.fst Δ[0] Δ[k] ≫ SSet.yonedaEquiv.symm (stageVertex r W) := by
  ext n z : 4
  change stageSimplexFunction r S n
    (((stages r).obj V).map z.1.down.op (stageVertex r V)) z.2 =
      ((stages r).obj W).map z.1.down.op (stageVertex r W)
  have hz : z.1.down = n.unop.const ⦋0⦌ 0 :=
    @Subsingleton.elim (n.unop ⟶ ⦋0⦌) inferInstance _ _
  rw [hz]
  exact stageSimplexFunction_zeroSimplex r S n z.2

/-- The realized higher family fixes the actual original stage point throughout. -/
theorem stageSimplexRealization_fixed_point (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} {k : ℕ}
    (S : ModelSimplex V W k) (z : |(Δ[k] : SSet.{u})|) :
    stageSimplexRealization r S (stagePoint r V, z) = stagePoint r W := by
  let p := (realizationProductSimplexIso (Δ[0] : SSet.{u}) k).inv (default, z)
  have hn := ConcreteCategory.congr_hom
    (realizationProductSimplexIso_inv_whisker (SSet.yonedaEquiv.symm (stageVertex r V)) k)
    (default, z)
  change SSet.toTop.map (SSet.yonedaEquiv.symm (stageVertex r V) ▷ Δ[k]) p =
    (realizationProductSimplexIso ((stages r).obj V) k).inv (stagePoint r V, z) at hn
  change SSet.toTop.map (stageTransformationSimplex r S)
    ((realizationProductSimplexIso ((stages r).obj V) k).inv (stagePoint r V, z)) = _
  rw [← hn]
  change (SSet.toTop.map (SSet.yonedaEquiv.symm (stageVertex r V) ▷ Δ[k]) ≫
    SSet.toTop.map (stageTransformationSimplex r S)) p = _
  rw [← Functor.map_comp, stageTransformationSimplex_fixed_vertex,
    Functor.map_comp, TopCat.comp_app]
  rw [Subsingleton.elim (SSet.toTop.map (CartesianMonoidalCategory.fst Δ[0] Δ[k]) p) default]
  rfl

end CategoryTheory.Waldhausen.IteratedS
