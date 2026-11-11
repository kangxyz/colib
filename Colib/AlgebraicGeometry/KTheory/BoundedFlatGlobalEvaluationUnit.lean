/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationNaturality
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullbackUnit
public import Colib.CategoryTheory.Functor.IdentityAutomorphismSquare

/-! # Original unit transport through the actual global evaluation comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
      CategoryTheory.Functor.IdentityAutomorphism
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
attribute [local irreducible] boundedAboveFlatGlobalSectionEvaluation
      boundedAboveFlatPerfectGlobalUnitIso

/-- The native AsSmall lowering functor is an equivalence on the original bounded-above flat
perfect category. -/
local instance evaluationRawUnitDownEquivalence {X : Scheme.{u}} :
    (AsSmall.down : AsSmall.{0} ((boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory) ⥤
      (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory).IsEquivalence :=
  AsSmall.equiv.symm.isEquivalence_functor

/-- The unchanged original raw geometric unit, with its actual zero normalization and lift. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationUnit.lean:27"
  "adaptation" "Original full evaluation comparison and both zero normalizations"]
def evaluationRawUnit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    (evaluationRawMap f).hom.toFunctor ⟶
      (evaluationRawMap f).hom.toFunctor :=
  whiskerLeft AsSmall.down (whiskerRight
    (normalizedWeakTransformation
      (boundedAboveFlatPerfectPullback_isExact f)
      (boundedAboveFlatPerfectPullback_isExact f)
      (boundedAboveFlatPerfectPullbackUnitIso
        f r).hom) AsSmall.up)

/-- Its forward component is exactly the same target unit on the actual normalized raw functor. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationUnit.lean:39"
  "adaptation" "Original full evaluation comparison and both zero normalizations"]
theorem evaluationRawUnit_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    evaluationRawUnit f r =
      (onFunctor (evaluationRawMap f).hom.toFunctor
        (evaluationSmallUnit (Opposite.op X) r)).hom := by
  apply NatTrans.ext
  funext K
  change AsSmall.{0} ((boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory) at K
  apply (AsSmall.down : AsSmall.{0} ((boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory) ⥤
    (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory).map_injective
  rw [onFunctor_hom_app, evaluationSmallUnit, map_lift_hom]
  simp only [evaluationRawUnit, whiskerLeft_app, whiskerRight_app,
    AsSmall.down_map, AsSmall.up_map_down, normalizedWeakTransformation, NatTrans.comp_app]
  let p := boundedAboveFlatPerfectPullback f
  let h := boundedAboveFlatPerfectPullback_isExact f
  let q := CategoryTheory.rebaseFunctor p
    (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).zero
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).zero
    ((h.zero (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).isZero).iso
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).isZero)
  let z : p ≅ q := CategoryTheory.rebaseFunctorIso _ _ _ _
  simp only [boundedAboveFlatPerfectPullbackUnitIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom]
  have hn := (boundedAboveFlatPerfectGlobalUnitIso X r).hom.naturality
    (z.hom.app (AsSmall.down.obj K))
  simp only [Functor.id_map, Functor.id_obj] at hn
  change z.inv.app (AsSmall.down.obj K) ≫
      (boundedAboveFlatPerfectGlobalUnitIso X r).hom.app
        (p.obj (AsSmall.down.obj K)) ≫ z.hom.app (AsSmall.down.obj K) =
    (boundedAboveFlatPerfectGlobalUnitIso X r).hom.app (q.obj (AsSmall.down.obj K))
  rw [← hn, Iso.inv_hom_id_app_assoc]

/-- The full actual evaluation comparison intertwines both original normalized units. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEvaluationUnit.lean:72"
  "adaptation" "Original full evaluation comparison and both zero normalizations"]
theorem evaluation_unit_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    whiskerRight (onFunctor (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor
        (boundedAboveFlatGlobalSectionUnit (Opposite.op X) r)).hom (evaluationModel (Opposite.op
      X)).hom.toFunctor ≫
      (evaluationComparisonIso f).hom =
    (evaluationComparisonIso f).hom ≫
      whiskerLeft (evaluationModel (Opposite.op Y)).hom.toFunctor (evaluationRawUnit f r) := by
  rw [evaluationRawUnit_eq]
  exact onFunctor_whisker_square (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor
    (evaluationRawMap f).hom.toFunctor (evaluationModel (Opposite.op Y)).hom.toFunctor
    (evaluationModel (Opposite.op X)).hom.toFunctor (evaluationComparisonIso f).hom
    (boundedAboveFlatGlobalSectionUnit (Opposite.op X) r) (evaluationSmallUnit (Opposite.op X) r)
    (evaluationModel_unit (Opposite.op X) r).whisker

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

attribute [colib_tag "COL-0548"] evaluation_unit_square

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
