/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.UniverseNaturality
public import Colib.CategoryTheory.TheoremB.NaturalTransformationFiberLift
public import Colib.Topology.HomotopyFiber.Map

/-!
# Promotion of the original natural-transformation cylinder

The native simplex-colimit descent preserves both coordinates of the realized
nerve cylinder. No replacement simplicial-map or geometric-realization model
is introduced. This retains the full original nullhomotopy, not only its endpoints.

Implementation source: `Quillen/Topology/ClassifyingSpace/UniversePromotion.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite Convexity SSet
open Topology
open scoped Simplicial Topology unitInterval
namespace CategoryTheory.UniversePromotion

/-- The original nerve cylinder map obtained by native simplex descent. -/
def cylinderMap {C : Type u} [SmallCategory C] {D : Type v} [SmallCategory D]
    (F : C ⥤ D) : C(|nerve C ⊗ (Δ[1] : SSet.{u})|, |nerve D ⊗ (Δ[1] : SSet.{v})|) :=
  realizationDesc (fun n x => realizationSimplex (X := nerve D ⊗ (Δ[1] : SSet.{v}))
    (n := n) (x.1 ⋙ F, ULift.up x.2.down)) (by
      intro n m a x t
      exact realizationSimplex_naturality (X := nerve D ⊗ (Δ[1] : SSet.{v}))
        a (x.1 ⋙ F, ULift.up x.2.down) t)

private theorem cylinderMap_simplex {C : Type u} [SmallCategory C]
    {D : Type v} [SmallCategory D] (F : C ⥤ D) (n : SimplexCategory)
    (x : (nerve C ⊗ (Δ[1] : SSet.{u})).obj (op n))
    (t : StdSimplex ℝ (Fin (n.len + 1))) :
    cylinderMap F (realizationSimplex x t) =
      realizationSimplex (X := nerve D ⊗ (Δ[1] : SSet.{v})) (x.1 ⋙ F, ULift.up x.2.down) t := by
  unfold cylinderMap
  rw [realizationDesc_simplex]
  intro n m a x t
  exact realizationSimplex_naturality (X := nerve D ⊗ (Δ[1] : SSet.{v}))
    a (x.1 ⋙ F, ULift.up x.2.down) t


private theorem realizationMap_simplex {X Y : SSet.{u}} (f : X ⟶ Y) (n : SimplexCategory)
    (x : X.obj (op n)) (t : StdSimplex ℝ (Fin (n.len + 1))) :
    SSet.toTop.map f (realizationSimplex x t) = realizationSimplex (f.app (op n) x) t := by
  change (SSet.toTop.map (SSet.yonedaEquiv.symm x) ≫ SSet.toTop.map f)
    ((SimplexCategory.toTopHomeo n).symm t) = _
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp]
  rfl

private theorem intervalCoordinate_simplex (n : SimplexCategory)
    (a : (Δ[1] : SSet.{u}).obj (op n)) (t : StdSimplex ℝ (Fin (n.len + 1))) :
    (SSet.stdSimplex.toTopObjIsoI.hom (realizationSimplex a t)).down =
      StdSimplex.homeomorphI (StdSimplex.map a.down.toOrderHom t) := by
  have ha : SSet.yonedaEquiv.symm a = SSet.stdSimplex.map a.down := by
    ext m b
    rfl
  change (SSet.stdSimplex.toTopObjIsoI.hom
    (SSet.toTop.map (SSet.yonedaEquiv.symm a) ((SimplexCategory.toTopHomeo n).symm t))).down = _
  rw [ha]
  change StdSimplex.homeomorphI (SimplexCategory.toTopHomeo ⦋1⦌
    (SSet.toTop.map (SSet.stdSimplex.map a.down) ((SimplexCategory.toTopHomeo n).symm t))) = _
  rw [SimplexCategory.toTopHomeo_naturality_apply, Homeomorph.apply_symm_apply]
  rfl

/-- Promotion preserves both actual realized cylinder coordinates. -/
theorem cylinderComparison_universe {C : Type u} [SmallCategory C]
    {D : Type v} [SmallCategory D] (F : C ⥤ D)
    (z : |nerve C ⊗ (Δ[1] : SSet.{u})|) :
    (realizationCylinderIso (nerve D)).hom (cylinderMap F z) =
      (classifyingSpaceMapUniversal F ((realizationCylinderIso (nerve C)).hom z).1,
        ULift.up (((realizationCylinderIso (nerve C)).hom z).2.down)) := by
  have h : (fun z => (realizationCylinderIso (nerve D)).hom (cylinderMap F z)) =
      (fun z => (classifyingSpaceMapUniversal F ((realizationCylinderIso (nerve C)).hom z).1,
        ULift.up (((realizationCylinderIso (nerve C)).hom z).2.down))) := by
    apply realization_ext
    intro n x t
    rw [cylinderMap_simplex]
    apply Prod.ext
    · change SSet.toTop.map (fst (nerve D) Δ[1])
          (realizationSimplex (x.1 ⋙ F, ULift.up x.2.down) t) =
        classifyingSpaceMapUniversal F
          (SSet.toTop.map (fst (nerve C) Δ[1]) (realizationSimplex x t))
      rw [realizationMap_simplex, realizationMap_simplex, classifyingSpaceMapUniversal_simplex]
      rfl
    · apply ULift.ext
      change (SSet.stdSimplex.toTopObjIsoI.hom
        (SSet.toTop.map (snd (nerve D) Δ[1])
          (realizationSimplex (x.1 ⋙ F, ULift.up x.2.down) t))).down =
        (SSet.stdSimplex.toTopObjIsoI.hom
          (SSet.toTop.map (snd (nerve C) Δ[1]) (realizationSimplex x t))).down
      rw [realizationMap_simplex, realizationMap_simplex,
        intervalCoordinate_simplex, intervalCoordinate_simplex]
      rfl
  exact congrFun h z

private theorem cylinderInverse_universe {C : Type u} [SmallCategory C]
    {D : Type v} [SmallCategory D] (F : C ⥤ D)
    (x : ClassifyingSpace C) (t : unitInterval) :
    cylinderMap F ((realizationCylinderIso (nerve C)).inv (x, ULift.up t)) =
      (realizationCylinderIso (nerve D)).inv (classifyingSpaceMapUniversal F x, ULift.up t) := by
  apply (TopCat.homeoOfIso (realizationCylinderIso (nerve D))).injective
  change (realizationCylinderIso (nerve D)).hom
      (cylinderMap F ((realizationCylinderIso (nerve C)).inv (x, ULift.up t))) =
    (realizationCylinderIso (nerve D)).hom
      ((realizationCylinderIso (nerve D)).inv (classifyingSpaceMapUniversal F x, ULift.up t))
  have hx := ConcreteCategory.congr_hom (realizationCylinderIso (nerve C)).inv_hom_id
    (x, ULift.up t)
  have hy := ConcreteCategory.congr_hom (realizationCylinderIso (nerve D)).inv_hom_id
    (classifyingSpaceMapUniversal F x, ULift.up t)
  change (realizationCylinderIso (nerve C)).hom
    ((realizationCylinderIso (nerve C)).inv (x, ULift.up t)) = (x, ULift.up t) at hx
  change (realizationCylinderIso (nerve D)).hom
    ((realizationCylinderIso (nerve D)).inv (classifyingSpaceMapUniversal F x, ULift.up t)) =
    (classifyingSpaceMapUniversal F x, ULift.up t) at hy
  rw [cylinderComparison_universe, hx, hy]

variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- Lift the original functor using the native up/down functors. -/
abbrev liftedFunctor (F : C ⥤ D) : AsSmall.{max u v} C ⥤ AsSmall.{max u v} D :=
  AsSmall.down ⋙ F ⋙ AsSmall.up

/-- The original natural transformation with both categorical universes lifted. -/
def liftTransformation {F G : C ⥤ D} (α : F ⟶ G) :
    liftedFunctor.{u,v} F ⟶ liftedFunctor.{u,v} G :=
  Functor.whiskerLeft AsSmall.down (Functor.whiskerRight α AsSmall.up)

private theorem liftedCylinderFunctorSquare {F G : C ⥤ D} (α : F ⟶ G) :
    ((𝟭 (Fin 2)).prod (AsSmall.up : C ⥤ AsSmall.{max u v} C)) ⋙
      naturalTransformationCylinderFunctor (liftTransformation.{u,v} α) =
    naturalTransformationCylinderFunctor α ⋙ (AsSmall.up : D ⥤ AsSmall.{max u v} D) := by
  apply Functor.curry_obj_injective
  refine ComposableArrows.ext₁ rfl rfl ?_
  ext a
  apply ULift.ext
  simp [naturalTransformationCylinderFunctor, Functor.curry, Functor.curryObj,
    Functor.uncurry, ComposableArrows.mk₁, ComposableArrows.hom,
    liftTransformation, liftedFunctor, AsSmall.down, AsSmall.up, down_comp]

private theorem naturalCylinder_lift_map {F G : C ⥤ D} (α : F ⟶ G) :
    (classifyingSpaceMapUniversal (AsSmall.up : D ⥤ AsSmall.{max u v} D)).comp
      (SSet.toTop.map (naturalTransformationNerveCylinder α)).hom =
    (SSet.toTop.map (naturalTransformationNerveCylinder (liftTransformation.{u,v} α))).hom.comp
      (cylinderMap (AsSmall.up : C ⥤ AsSmall.{max u v} C)) := by
  apply DFunLike.coe_injective
  apply realization_ext
  intro n z t
  change classifyingSpaceMapUniversal (AsSmall.up : D ⥤ AsSmall.{max u v} D)
      (SSet.toTop.map (naturalTransformationNerveCylinder α) (realizationSimplex z t)) =
    SSet.toTop.map (naturalTransformationNerveCylinder (liftTransformation.{u,v} α))
      (cylinderMap (AsSmall.up : C ⥤ AsSmall.{max u v} C) (realizationSimplex z t))
  rw [realizationMap_simplex, classifyingSpaceMapUniversal_simplex,
    cylinderMap_simplex, realizationMap_simplex]
  apply congrArg (fun b => realizationSimplex b t)
  change (z.2.down.toOrderHom.monotone.functor.prod' z.1) ⋙
      (naturalTransformationCylinderFunctor α ⋙ AsSmall.up) =
    (z.2.down.toOrderHom.monotone.functor.prod' z.1) ⋙
      (((𝟭 (Fin 2)).prod (AsSmall.up : C ⥤ AsSmall.{max u v} C)) ⋙
        naturalTransformationCylinderFunctor (liftTransformation.{u,v} α))
  rw [liftedCylinderFunctorSquare]

/-- Lifting retains every point of the original homotopy and its interval parameter. -/
theorem naturalTransformationHomotopy_up {F G : C ⥤ D} (α : F ⟶ G)
    (t : unitInterval) (x : ClassifyingSpace C) :
    classifyingSpaceNaturalTransformationHomotopy (liftTransformation.{u,v} α)
      (t, classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{max u v} C) x) =
    classifyingSpaceMapUniversal (AsSmall.up : D ⥤ AsSmall.{max u v} D)
      (classifyingSpaceNaturalTransformationHomotopy α (t,x)) := by
  change SSet.toTop.map (naturalTransformationNerveCylinder (liftTransformation.{u,v} α))
      ((realizationCylinderIso (nerve (AsSmall.{max u v} C))).inv
        (classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{max u v} C) x, ULift.up t)) =
    classifyingSpaceMapUniversal (AsSmall.up : D ⥤ AsSmall.{max u v} D)
      (SSet.toTop.map (naturalTransformationNerveCylinder α)
        ((realizationCylinderIso (nerve C)).inv (x, ULift.up t)))
  rw [← cylinderInverse_universe]
  exact (ContinuousMap.congr_fun (naturalCylinder_lift_map.{u,v} α)
    ((realizationCylinderIso (nerve C)).inv (x, ULift.up t))).symm

end CategoryTheory.UniversePromotion

namespace CategoryTheory.UniversePromotion
variable {A C D : Type u} [SmallCategory A] [SmallCategory C] [SmallCategory D]

/-- The original row map commutes strictly with the actual universe maps. -/
theorem liftedRowSquare (F : C ⥤ D) :
    (classifyingSpaceMapUniversal (AsSmall.up : D ⥤ AsSmall.{max u v} D)).comp
      (classifyingSpaceMap F).hom =
    (classifyingSpaceMap (liftedFunctor.{u,v} F)).hom.comp
      (classifyingSpaceMapUniversal (AsSmall.up : C ⥤ AsSmall.{max u v} C)) := by
  rw [← classifyingSpaceMapUniversal_eq, ← classifyingSpaceMapUniversal_eq,
    ← classifyingSpaceMapUniversal_comp, ← classifyingSpaceMapUniversal_comp]
  rfl

/-- Promote a row fiber by the actual universe maps on its source and stored path. -/
def rowFiberUp (F : C ⥤ D) (d : D) :
    C(HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d),
      HomotopyFiber (classifyingSpaceMap (liftedFunctor.{u,v} F)).hom
        (classifyingSpacePoint (AsSmall.up.obj d))) where
  toFun z := ⟨(classifyingSpaceMapUniversal AsSmall.up z.val.1,
    (classifyingSpaceMapUniversal AsSmall.up).comp z.val.2),
    (congrArg (classifyingSpaceMapUniversal AsSmall.up) z.property.1).trans
      (ContinuousMap.congr_fun (liftedRowSquare.{u,v} F) z.val.1),
    (congrArg (classifyingSpaceMapUniversal AsSmall.up) z.property.2).trans
      (classifyingSpaceMapUniversal_point AsSmall.up d)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · exact (ContinuousMap.continuous_postcomp (classifyingSpaceMapUniversal AsSmall.up)).comp
        (continuous_snd.comp continuous_subtype_val)

/-- The original null transformation on the promoted categorical row. -/
def liftNullTransformation (P : A ⥤ C) (F : C ⥤ D) (d : D)
    (ε : P ⋙ F ⟶ (Functor.const A).obj d) :
    liftedFunctor.{u,v} P ⋙ liftedFunctor.{u,v} F ⟶
      (Functor.const (AsSmall.{max u v} A)).obj (AsSmall.up.obj d) :=
  liftTransformation.{u,v} ε

/-- The complete natural-transformation fiber lift commutes with universe promotion. -/
theorem rowFiberUp_naturalLift (P : A ⥤ C) (F : C ⥤ D) (d : D)
    (ε : P ⋙ F ⟶ (Functor.const A).obj d) :
    (rowFiberUp.{u,v} F d).comp (TheoremB.naturalTransformationFiberLift P F d ε) =
    (TheoremB.naturalTransformationFiberLift (liftedFunctor.{u,v} P)
      (liftedFunctor.{u,v} F)
      (AsSmall.up.obj d) (liftNullTransformation.{u,v} P F d ε)).comp
        (classifyingSpaceMapUniversal (AsSmall.up : A ⥤ AsSmall.{max u v} A)) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · exact ContinuousMap.congr_fun (liftedRowSquare.{u,v} P) z
  · apply ContinuousMap.ext
    intro t
    exact (naturalTransformationHomotopy_up.{u,v} ε t z).symm

end CategoryTheory.UniversePromotion
