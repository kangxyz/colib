/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalUnitIdentityAction
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectUnitHomotopy
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPullback
public import Colib.CategoryTheory.Functor.IdentityAutomorphismRebase
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumIdentityAction
public import Colib.KTheory.Waldhausen.Iterated.SelfTrackKOperationLevelExt
public import Colib.KTheory.Waldhausen.Iterated.SelfTrackKOperationNaturality

/-!
# Actual pullback-unit tracks as target scalar identity actions

The full chosen-zero normalization and faithful small lift are retained.
Source: Quillen `GlobalUnitIdentityOperation.lean` and `GlobalUnitReferenceNaturality.lean`
at revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 4000
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalUnitIdentityOperation
attribute [local irreducible] boundedAboveFlatPerfectGlobalUnitIso
private instance smallDownIsEquivalence {X : Scheme.{u}} :
    (AsSmall.down : AsSmall.{0}
      (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory ⥤
      (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory).IsEquivalence :=
  (AsSmall.equiv : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory ≌
    AsSmall.{0}
      (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory).isEquivalence_inverse

/-- Faithful lowering retains the entire lifted scalar identity action. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalUnitIdentityOperation.lean:47"
  "adaptation" "Actual normalized pullback, complete tracks and original scalar operations."]
theorem small_onFunctor {X Y : Scheme.{u}}
    (F : (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory ⥤
      (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory)
    (r : (Γ(X, ⊤))ˣ) :
    isoWhiskerLeft AsSmall.down
      (isoWhiskerRight (onFunctor F (boundedAboveFlatPerfectGlobalUnitIso X r)) AsSmall.up) =
    onFunctor (AsSmall.down ⋙ F ⋙ AsSmall.up) (ProductSwapUnit.smallUnit X r) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply (AsSmall.down : AsSmall.{0}
      (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory ⥤
    (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory).map_injective
  change AsSmall.down.{u, u + 1, 0}.map
      (AsSmall.up.{u, u + 1, 0}.map
        ((onFunctor F (boundedAboveFlatPerfectGlobalUnitIso X r)).hom.app (ULift.down K))) =
    AsSmall.down.{u, u + 1, 0}.map
      ((ProductSwapUnit.smallUnit X r).hom.app
        (AsSmall.up.{u, u + 1, 0}.obj (F.obj (ULift.down K))))
  calc
    _ = (boundedAboveFlatPerfectGlobalUnitIso X r).hom.app (F.obj (ULift.down K)) := by
      simp only [AsSmall.down_map, AsSmall.up_map_down, onFunctor_hom_app]
    _ = _ := (map_lift_hom
      (AsSmall.down.{u, u + 1, 0} : AsSmall.{0}
      (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory ⥤
        (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory)
      (boundedAboveFlatPerfectGlobalUnitIso X r)
      (AsSmall.up.{u, u + 1, 0}.obj (F.obj (ULift.down K)))).symm

/-- Actual zero normalization retains the target scalar action on pullback. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalUnitReferenceNaturality.lean:40"
  "adaptation" "Actual normalized pullback, complete tracks and original scalar operations."]
theorem normalizedUnit_eq_onFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    normalizedWeakTransformation (boundedAboveFlatPerfectPullback_isExact f)
      (boundedAboveFlatPerfectPullback_isExact f)
      (boundedAboveFlatPerfectPullbackUnitIso f r).hom =
    (onFunctor _ (boundedAboveFlatPerfectGlobalUnitIso X r)).hom := by
  apply NatTrans.ext
  funext K
  let e := rebaseFunctorIso (boundedAboveFlatPerfectPullback f)
    (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).zero
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).zero
    (((boundedAboveFlatPerfectPullback_isExact f).zero
      (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).isZero).iso
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).isZero)
  have hn := (boundedAboveFlatPerfectGlobalUnitIso X r).hom.naturality (e.hom.app K)
  simp only [Functor.id_map, Functor.id_obj] at hn
  change e.inv.app K ≫
    (boundedAboveFlatPerfectPullbackUnitIso f r).hom.app K ≫ e.hom.app K = _
  simp only [boundedAboveFlatPerfectPullbackUnitIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, rightUnitor_inv_app, rightUnitor_hom_app,
    isoWhiskerLeft_hom, whiskerLeft_app, Category.id_comp]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.comp_id]
  rw [← hn, Iso.inv_hom_id_app_assoc]
  rfl

/-- Every original time and spectrum level retains the target scalar action. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalUnitIdentityOperation.lean:85"
  "adaptation" "Actual normalized pullback, complete tracks and original scalar operations."]
theorem originalUnit_level {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (n : ℕ) :
    (boundedAboveFlatPerfectUnitHomotopy f r).level n =
      ((prespectrumIsoHomotopy
        (𝟙 (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))
        (ProductSwapUnit.smallUnit X r)).precomp
          (boundedAboveFlatPerfectPullbackPrespectrumMap f)).level n := by
  let M := asSmallCategoryMap (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
    (boundedAboveFlatPerfectPullback_isExact f).rebase (rebaseFunctor_obj_base _ _ _ _)
  refine Eq.trans ?_ (prespectrumIsoHomotopy_onFunctor_level M
    (ProductSwapUnit.smallUnit X r) n)
  unfold boundedAboveFlatPerfectUnitHomotopy exactOriginalPrespectrumIsoHomotopy
    exactOriginalPrespectrumHomotopy originalPrespectrumTransformationHomotopy
    prespectrumIsoHomotopy
  congr 2
  rw [normalizedUnit_eq_onFunctor]
  exact congrArg Iso.hom (small_onFunctor _ r)

/-- The literal geometric unit factors through its actual original pullback K-map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalUnitIdentityOperation.lean:99"
  "adaptation" "Actual normalized pullback, complete tracks and original scalar operations."]
theorem originalUnit_operation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (n : ℕ) :
    originalKSelfTrackOperation (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
      (boundedAboveFlatPerfectUnitHomotopy f r) n =
      (unitKOperation X r n).comp (boundedAboveFlatPerfectKPullback f n) := by
  rw [originalKSelfTrackOperation_eq_of_levels
    (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
    (boundedAboveFlatPerfectUnitHomotopy f r) _ (originalUnit_level f r)]
  exact originalKSelfTrackOperation_precomp
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
    (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace) _
    (boundedAboveFlatPerfectPullback_isExact f) n
/-- The original scalar at the identity projection is the target identity action. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalUnitIdentityOperation.lean:114"
  "adaptation" "Actual normalized pullback, complete tracks and original scalar operations."]
theorem originalIdentityUnit_operation (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) (n : ℕ) :
    originalKSelfTrackOperation (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
      (boundedAboveFlatPerfectUnitHomotopy (𝟙 X) r) n = unitKOperation X r n := by
  rw [originalUnit_operation, boundedAboveFlatPerfectKPullback_id, MonoidHom.comp_id]

/-- The actual small normalized pullback preserves the forward pulled-back scalar. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalUnitReferenceNaturality.lean:110"
  "adaptation" "Actual normalized pullback, complete tracks and original scalar operations."]
theorem normalizedModel_preserves {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(Y, ⊤))ˣ) :
    Preserves
      (asSmallCategoryMap (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
        (boundedAboveFlatPerfectPullback_isExact f).rebase
        (rebaseFunctor_obj_base _ _ _ _)).hom.toFunctor
      (ProductSwapUnit.smallUnit Y r)
      (ProductSwapUnit.smallUnit X (Units.map f.appTop.hom.toMonoidHom r)) := by
  intro K
  apply (AsSmall.down : AsSmall.{0}
    (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory ⥤
    (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory).map_injective
  change (rebaseFunctor (boundedAboveFlatPerfectPullback f) _ _ _).map
      (AsSmall.down.map ((ProductSwapUnit.smallUnit Y r).hom.app K)) =
    AsSmall.down.map
      ((ProductSwapUnit.smallUnit X (Units.map f.appTop.hom.toMonoidHom r)).hom.app
        (AsSmall.up.obj
          ((rebaseFunctor (boundedAboveFlatPerfectPullback f) _ _ _).obj
            (AsSmall.down.obj K))))
  rw [ProductSwapUnit.smallUnit, map_lift_hom, ProductSwapUnit.smallUnit, map_lift_hom]
  exact rebase_preserves (boundedAboveFlatPerfectPullback f) _ _ _ _ _
    (boundedAboveFlatPerfectPullback_map_globalUnit f r) (AsSmall.down.obj K)

/-- Every time slice of the actual scalar track is natural under arbitrary pullback. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProductSwapUnit.lean:128"
  "adaptation" "Actual normalized pullback, complete tracks and original scalar operations."]
theorem unitTrack_pullback_level {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(Y, ⊤))ˣ) (n : ℕ) :
    ((prespectrumIsoHomotopy
      (𝟙 (asSmallCategory (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)))
      (ProductSwapUnit.smallUnit Y r)).postcomp
        (boundedAboveFlatPerfectPullbackPrespectrumMap f)).level n =
    ((prespectrumIsoHomotopy
      (𝟙 (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)))
      (ProductSwapUnit.smallUnit X (Units.map f.appTop.hom.toMonoidHom r))).precomp
        (boundedAboveFlatPerfectPullbackPrespectrumMap f)).level n := by
  apply ContinuousMap.ext
  intro z
  let M := asSmallCategoryMap (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
    (boundedAboveFlatPerfectPullback_isExact f).rebase (rebaseFunctor_obj_base _ _ _ _)
  have he := (normalizedModel_preserves f r).whisker
  exact prespectrumIsoHomotopy_square_apply (𝟙 _) (𝟙 _) M M
    (ProductSwapUnit.smallUnit Y r)
    (ProductSwapUnit.smallUnit X (Units.map f.appTop.hom.toMonoidHom r))
    (by simp) (by simpa using he) n z.1 z.2

/-- Arbitrary actual pullback preserves the original scalar identity operation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalUnitIdentityOperation.lean:121"
  "adaptation" "Actual normalized pullback, complete tracks and original scalar operations."]
theorem unitKOperation_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(Y, ⊤))ˣ) (n : ℕ) :
    (boundedAboveFlatPerfectKPullback f (n + 1)).comp (unitKOperation Y r n) =
      (unitKOperation X (Units.map f.appTop.hom.toMonoidHom r) n).comp
        (boundedAboveFlatPerfectKPullback f n) := by
  unfold unitKOperation boundedAboveFlatPerfectKPullback
  rw [← originalKSelfTrackOperation_postcomp, ← originalKSelfTrackOperation_precomp]
  exact originalKSelfTrackOperation_eq_of_levels _ _ _ _ (unitTrack_pullback_level f r) n

end AlgebraicGeometry.Scheme.Modules.GlobalUnitIdentityOperation
