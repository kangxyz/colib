/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.IdentityCylinder
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopy

/-!
# Identity transformations give the constant prespectrum track

For every strict zero-preserving exact model map, the actual natural-transformation
homotopy of its identity transformation is the reflexive homotopy. The equality retains
the entire simplicial cylinder, every realization time and the degree-zero based loops.
No weakness assumption on a zero endotransformation is needed.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial Topology unitInterval

universe u

namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology

/-- The actual quotient-row transformation preserves the identity transformation. -/
lemma rowsTransformation_identity {V W : WideSubcategory preservesZero.{u}}
    (F : V ⟶ W) (n : SimplexCategory) :
    rowsTransformation (𝟙 F.hom.toFunctor) n = 𝟙 ((rows n).map F).hom.toFunctor := by
  apply NatTrans.ext
  funext A
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext p
  rfl

/-- Every cut of the identity transformation at every iterated stage is the actual stage map. -/
lemma stageTransformationFunction_identity (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)
    (hη : ∀ A, W.obj.waldhausen.weq (𝟙 (F.hom.toFunctor.obj A)))
    (n : SimplexCategoryᵒᵖ) (A : ((stages r).obj V).obj n) (τ : (Δ[1]).obj n) :
    stageTransformationFunction r (𝟙 F.hom.toFunctor) hη n A τ =
      ((stages r).map F).app n A := by
  induction r generalizing V W with
  | zero =>
    apply Subtype.ext
    change nerveCylinderDiagram (𝟙 (A.val ⋙ F.hom.toFunctor)) τ.down =
      A.val ⋙ F.hom.toFunctor
    exact nerveCylinderDiagram_identity _ _
  | succ r ih =>
    change stageTransformationFunction r
      (rowsTransformation (𝟙 F.hom.toFunctor) n.unop)
      (rowsTransformation_weak (𝟙 F.hom.toFunctor) hη n.unop) n A τ =
        ((stages r).map ((rows n.unop).map F)).app n A
    simpa only [rowsTransformation_identity] using
      (ih ((rows n.unop).map F)
        (fun B ↦ ((rows n.unop).obj W).obj.waldhausen.weq.id_mem
          (((rows n.unop).map F).hom.toFunctor.obj B)) A)

/-- The whole identity cylinder is the projection followed by the original stage map. -/
lemma stageTransformationCylinder_identity (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)
    (hη : ∀ A, W.obj.waldhausen.weq (𝟙 (F.hom.toFunctor.obj A))) :
    stageTransformationCylinder r (𝟙 F.hom.toFunctor) hη =
      CartesianMonoidalCategory.fst ((stages r).obj V) Δ[1] ≫ (stages r).map F := by
  ext n z : 4
  exact stageTransformationFunction_identity r F hη n z.1 z.2

/-- Every time of the actual realized identity cylinder is the original realized map. -/
lemma stageTransformationTopHomotopy_identity (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)
    (hη : ∀ A, W.obj.waldhausen.weq (𝟙 (F.hom.toFunctor.obj A)))
    (s : unitInterval) (x : stageSpace r V) :
    stageTransformationTopHomotopy r (𝟙 F.hom.toFunctor) hη (s, x) =
      SSet.toTop.map ((stages r).map F) x := by
  have hp : (realizationCylinderIso ((stages r).obj V)).inv ≫
      SSet.toTop.map (CartesianMonoidalCategory.fst ((stages r).obj V) Δ[1]) =
        CartesianMonoidalCategory.fst _ _ := by
    rw [← realizationCylinderComparison_fst]
    change (realizationCylinderIso ((stages r).obj V)).inv ≫
      (realizationCylinderIso ((stages r).obj V)).hom ≫ _ = _
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change SSet.toTop.map (stageTransformationCylinder r (𝟙 F.hom.toFunctor) hη)
    ((realizationCylinderIso ((stages r).obj V)).inv (x, ULift.up s)) = _
  rw [stageTransformationCylinder_identity, SSet.toTop.map_comp]
  change ((realizationCylinderIso ((stages r).obj V)).inv ≫
    SSet.toTop.map (CartesianMonoidalCategory.fst ((stages r).obj V) Δ[1]) ≫
      SSet.toTop.map ((stages r).map F)) (x, ULift.up s) = _
  rw [← Category.assoc, hp]
  rfl

/-- The original identity track is constant at every level, including its actual loop level. -/
lemma prespectrumTransformationHomotopy_identity_level
    {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)
    (hη : ∀ A, W.obj.waldhausen.weq (𝟙 (F.hom.toFunctor.obj A))) (n : ℕ) :
    (prespectrumTransformationHomotopy (𝟙 F.hom.toFunctor) hη).level n =
      (LoopPrespectrum.Homotopy.refl (prespectrumMap F)).level n := by
  cases n with
  | zero =>
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    change Path (stagePoint 0 V) (stagePoint 0 V) at x
    apply Path.ext
    funext q
    exact stageTransformationTopHomotopy_identity 0 F hη s (x q)
  | succ r =>
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    exact stageTransformationTopHomotopy_identity r F hη s x

/-- The actual identity-transformation prespectrum homotopy is exactly the reflexive track. -/
theorem prespectrumTransformationHomotopy_identity
    {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)
    (hη : ∀ A, W.obj.waldhausen.weq (𝟙 (F.hom.toFunctor.obj A))) :
    prespectrumTransformationHomotopy (𝟙 F.hom.toFunctor) hη =
      LoopPrespectrum.Homotopy.refl (prespectrumMap F) := by
  apply LoopPrespectrum.Homotopy.ext
  funext n
  exact prespectrumTransformationHomotopy_identity_level F hη n

end CategoryTheory.Waldhausen.IteratedS
