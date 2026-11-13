/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.IntervalLocalization
public import Colib.CategoryTheory.Sites.Simplicial.ParameterProductFreeAbelian
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-!
# Reduced free abelian chains of a representable parameter cylinder

Free abelianization preserves the pushout which collapses the basepoint axis.
The cokernel of the axis is the reduction of the cylinder. Comparing the axis
and product with the parameter coproduct gives the original reduced generators
and carries the cylinder projection to the degreewise fold.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C]

section Axis

variable (I : Cᵒᵖ ⥤ SSet.{w})

private abbrev parameterCylinderInclusion (X : PointedSimplicialPresheaf.{w} C) :
    X.right ⨯ I ⟶ (parameterizedCylinder X I).right :=
  pushout.inl (intervalAxis X I) (terminal.from I)

private theorem freeAbelianAxisPushout (X : PointedSimplicialPresheaf.{w} C) :
    IsPushout ((freeAbelian C).map (intervalAxis X I)) ((freeAbelian C).map (terminal.from I))
      ((freeAbelian C).map (parameterCylinderInclusion I X))
      ((freeAbelian C).map (parameterizedCylinder X I).hom) :=
  (freeAbelian C).map_isPushout (IsPushout.of_hasPushout (intervalAxis X I) (terminal.from I))

private def axisCokernelIso (X : PointedSimplicialPresheaf.{w} C) :
    cokernel ((freeAbelian C).map (intervalAxis X I)) ≅
      (reducedFreeAbelian C).obj (parameterizedCylinder X I) :=
  let sq := freeAbelianAxisPushout I X
  @asIso _ _ _ _ (cokernel.map _ _ _ _ sq.w) (isIso_cokernel_map_of_isPushout sq)

@[reassoc]
private theorem axisCokernelIso_π_hom (X : PointedSimplicialPresheaf.{w} C) :
    cokernel.π ((freeAbelian C).map (intervalAxis X I)) ≫ (axisCokernelIso I X).hom =
      (freeAbelian C).map (parameterCylinderInclusion I X) ≫
        reduction C (parameterizedCylinder X I) := by
  let sq := freeAbelianAxisPushout I X
  change cokernel.π ((freeAbelian C).map (intervalAxis X I)) ≫
      cokernel.map _ _ _ _ sq.w =
    (freeAbelian C).map (parameterCylinderInclusion I X) ≫
      cokernel.π ((freeAbelian C).map (parameterizedCylinder X I).hom)
  simp only [cokernel.map, cokernel.π_desc]

/-- The actual product leg surjects onto the original reduced cylinder chains. -/
theorem epi_freeAbelianParameterCylinderInclusion (X : PointedSimplicialPresheaf.{w} C) :
    Epi ((freeAbelian C).map (pushout.inl (intervalAxis X I) (terminal.from I)) ≫
      reduction C (parameterizedCylinder X I)) := by
  rw [← axisCokernelIso_π_hom I X]
  infer_instance

end Axis

variable (V : C)

private def freeParameterAxisIso :
    (freeAbelian C).obj (liftedRepresentableInterval.{w} V) ≅
      (ParameterCoproduct.simplicialFunctor V AddCommGrpCat.{max v w}).obj
        ((freeAbelian C).obj (⊤_ (Cᵒᵖ ⥤ SSet.{max v w}))) :=
  let I := liftedRepresentableInterval.{w} V
  (freeAbelian C).mapIso (Limits.prod.leftUnitor I).symm ≪≫
    (freeAbelianParameterProductIso.{w} V).app (⊤_ _)

private theorem freeParameterAxisIso_comm (X : PointedSimplicialPresheaf.{max v w} C) :
    (freeAbelian C).map (intervalAxis X (liftedRepresentableInterval.{w} V)) ≫
        (freeAbelianParameterProductIso.{w} V).hom.app X.right =
      (freeParameterAxisIso.{w} V).hom ≫
        (ParameterCoproduct.simplicialFunctor V AddCommGrpCat.{max v w}).map
          ((freeAbelian C).map X.hom) := by
  let I := liftedRepresentableInterval.{w} V
  let F := freeAbelian.{max v w} C
  let Φ := ParameterCoproduct.simplicialFunctor V AddCommGrpCat.{max v w}
  let e := freeAbelianParameterProductIso.{w} V
  have h : intervalAxis X I = (Limits.prod.leftUnitor I).inv ≫ prod.map X.hom (𝟙 I) := by
    apply prod.hom_ext <;> simp [intervalAxis, Limits.prod.leftUnitor]
  change F.map (intervalAxis X I) ≫ e.hom.app X.right =
    (freeParameterAxisIso.{w} V).hom ≫ Φ.map (F.map X.hom)
  calc
    _ = F.map (Limits.prod.leftUnitor I).inv ≫ F.map (prod.map X.hom (𝟙 I)) ≫
        e.hom.app X.right := by rw [h, Functor.map_comp, Category.assoc]
    _ = F.map (Limits.prod.leftUnitor I).inv ≫ e.hom.app (⊤_ _) ≫ Φ.map (F.map X.hom) :=
      congrArg (F.map (Limits.prod.leftUnitor I).inv ≫ ·) (e.hom.naturality X.hom)
    _ = _ := (Category.assoc _ _ _).symm

local instance simplicialParameterCoproduct_preservesCokernels :
    PreservesColimitsOfShape WalkingParallelPair
      (ParameterCoproduct.simplicialFunctor V AddCommGrpCat.{max v w}) := by
  let P := ParameterCoproduct.functor V AddCommGrpCat.{max v w}
  let : PreservesFiniteColimits P := by
    change PreservesFiniteColimits
      (SlicePresheaf.restriction V ⋙ SlicePresheaf.extension V (A := AddCommGrpCat.{max v w}))
    infer_instance
  change PreservesColimitsOfShape WalkingParallelPair
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj P)
  infer_instance

/-- The actual reduced abelianization of the pointed cylinder is the parameter
coproduct of the original reduced abelianization in each simplicial degree. -/
@[no_expose]
def reducedFreeAbelianParameterCylinderIso (X : PointedSimplicialPresheaf.{max v w} C) :
    (reducedFreeAbelian C).obj (parameterizedCylinder X (liftedRepresentableInterval.{w} V)) ≅
      (ParameterCoproduct.simplicialFunctor V AddCommGrpCat.{max v w}).obj
        ((reducedFreeAbelian C).obj X) :=
  let I := liftedRepresentableInterval.{w} V
  let F := freeAbelian.{max v w} C
  let Φ := ParameterCoproduct.simplicialFunctor V AddCommGrpCat.{max v w}
  (axisCokernelIso I X).symm ≪≫
    (cokernel.mapIso (F.map (intervalAxis X I)) (Φ.map (F.map X.hom))
      (freeParameterAxisIso.{w} V) ((freeAbelianParameterProductIso.{w} V).app X.right)
      (freeParameterAxisIso_comm V X) ≪≫ (PreservesCokernel.iso Φ (F.map X.hom)).symm)

/-- The original reduced comparison retains the product map and the point quotient. -/
@[reassoc]
theorem cylinderInclusion_reduction_comp_iso (X : PointedSimplicialPresheaf.{max v w} C) :
    (freeAbelian C).map (pushout.inl (intervalAxis X (liftedRepresentableInterval.{w} V))
        (terminal.from (liftedRepresentableInterval.{w} V))) ≫
      reduction C (parameterizedCylinder X (liftedRepresentableInterval.{w} V)) ≫
        (reducedFreeAbelianParameterCylinderIso.{w} V X).hom =
      (freeAbelianParameterProductIso.{w} V).hom.app X.right ≫
        (ParameterCoproduct.simplicialFunctor V AddCommGrpCat.{max v w}).map (reduction C X) := by
  let I := liftedRepresentableInterval.{w} V
  let F := freeAbelian.{max v w} C
  let Φ := ParameterCoproduct.simplicialFunctor V AddCommGrpCat.{max v w}
  let t := F.map (intervalAxis X I)
  let b := F.map X.hom
  let a := axisCokernelIso I X
  let e := (freeAbelianParameterProductIso.{w} V).app X.right
  let c := cokernel.mapIso t (Φ.map b) (freeParameterAxisIso.{w} V) e
    (freeParameterAxisIso_comm V X)
  let d := PreservesCokernel.iso Φ b
  have hc : cokernel.π t ≫ c.hom = e.hom ≫ cokernel.π (Φ.map b) := by
    simp only [c, cokernel.mapIso_hom, cokernel.map, cokernel.π_desc]
  have hd : cokernel.π (Φ.map b) ≫ d.inv = Φ.map (reduction C X) := by
    rw [show d.inv = cokernelComparison b Φ from PreservesCokernel.iso_inv Φ b]
    exact π_comp_cokernelComparison b Φ
  change F.map (parameterCylinderInclusion I X) ≫ reduction C (parameterizedCylinder X I) ≫
    (a.inv ≫ c.hom ≫ d.inv) = _
  rw [← axisCokernelIso_π_hom_assoc I X, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, hc, Category.assoc, hd]
  rfl

/-- Reduction of the generator of a paired simplex belongs to the summand
indexed by its original parameter coordinate. -/
theorem reducedFreeAbelianParameterCylinderIso_hom_generator
    (X : PointedSimplicialPresheaf.{max v w} C) (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    let I := liftedRepresentableInterval.{w} V
    ∀ x : ((X.right ⨯ I).obj U).obj n,
      (((reducedFreeAbelianParameterCylinderIso.{w} V X).hom.app n).app U)
        (reducedGenerator C (parameterizedCylinder X I) n U
          (((pushout.inl (intervalAxis X I) (terminal.from I)).app U).app n x)) =
        ParameterCoproduct.ι V _ (((reducedFreeAbelian C).obj X).obj n) U
          (((prod.snd : X.right ⨯ I ⟶ I).app U).app n x).down
          (reducedGenerator C X n U (((prod.fst : X.right ⨯ I ⟶ X.right).app U).app n x)) := by
  intro I x
  let e := freeAbelianParameterProductIso.{w} V
  let f := (reduction C X).app n
  let Φ := ParameterCoproduct.functor V AddCommGrpCat.{max v w}
  let q := parameterCylinderInclusion I X
  let g := (((prod.snd : X.right ⨯ I ⟶ I).app U).app n x).down
  let y := ((prod.fst : X.right ⨯ I ⟶ X.right).app U).app n x
  have h := congrArg (fun a => (a.app n).app U (FreeAbelianGroup.of x))
    (cylinderInclusion_reduction_comp_iso.{w} V X)
  change (((reducedFreeAbelianParameterCylinderIso.{w} V X).hom.app n).app U)
      (((reduction C (parameterizedCylinder X I)).app n).app U
        (AddCommGrpCat.free.map ((q.app U).app n) (FreeAbelianGroup.of x))) =
    (Φ.map f).app U (((e.hom.app X.right).app n).app U (FreeAbelianGroup.of x)) at h
  rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of,
    freeAbelianParameterProductIso_hom_of] at h
  exact h.trans (ConcreteCategory.congr_hom (ParameterCoproduct.ι_map_app V _ f U g)
    (FreeAbelianGroup.of y))

/-- The actual cylinder projection becomes the fold on the reduced summands. -/
@[reassoc]
theorem reducedFreeAbelianParameterCylinderIso_hom_fold
    (X : PointedSimplicialPresheaf.{max v w} C) :
    (reducedFreeAbelianParameterCylinderIso.{w} V X).hom ≫
      (ParameterCoproduct.simplicialFold V _).app ((reducedFreeAbelian C).obj X) =
        (reducedFreeAbelian C).map (cylinderProjection X (liftedRepresentableInterval.{w} V)) := by
  let I := liftedRepresentableInterval.{w} V
  let F := freeAbelian.{max v w} C
  let Y := parameterizedCylinder X I
  let p := cylinderProjection X I
  let q := parameterCylinderInclusion I X
  let e := freeAbelianParameterProductIso.{w} V
  let Φ := ParameterCoproduct.simplicialFunctor V AddCommGrpCat.{max v w}
  let a := F.map q ≫ reduction C Y
  let : Epi a := by
    change Epi (F.map q ≫ reduction C Y)
    rw [← axisCokernelIso_π_hom I X]
    infer_instance
  have hp : q ≫ p.right = (prod.fst : X.right ⨯ I ⟶ X.right) := by
    change pushout.inl (intervalAxis X I) (terminal.from I) ≫
      pushout.desc (prod.fst : X.right ⨯ I ⟶ X.right) X.hom _ = _
    exact pushout.inl_desc _ _ _
  apply (cancel_epi a).1
  calc
    _ = e.hom.app X.right ≫ Φ.map (reduction C X) ≫
        (ParameterCoproduct.simplicialFold V _).app ((reducedFreeAbelian C).obj X) := by
      simpa only [a, Category.assoc] using
        cylinderInclusion_reduction_comp_iso_assoc.{w} V X
          ((ParameterCoproduct.simplicialFold V _).app ((reducedFreeAbelian C).obj X))
    _ = e.hom.app X.right ≫ (ParameterCoproduct.simplicialFold V _).app (F.obj X.right) ≫
        reduction C X := by rw [(ParameterCoproduct.simplicialFold V _).naturality, Functor.id_map]
    _ = F.map (prod.fst : X.right ⨯ I ⟶ X.right) ≫ reduction C X :=
      freeAbelianParameterProductIso_hom_fold_assoc V X.right (reduction C X)
    _ = a ≫ (reducedFreeAbelian C).map p := by
      change F.map (prod.fst : X.right ⨯ I ⟶ X.right) ≫ reduction C X =
        (F.map q ≫ reduction C Y) ≫ (reducedFreeAbelian C).map p
      rw [Category.assoc, reduction_naturality, ← Functor.map_comp_assoc, hp]

end CategoryTheory.PointedSimplicialPresheaf
