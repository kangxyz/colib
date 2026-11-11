/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorModelComparison
public import Colib.CategoryTheory.Functor.IdentityAutomorphismSquare

/-! # Genuine tensor multiplication through the actual Model comparison

The scalar identification is proved from the actual tensor unitor square and naturality.
Both selected-zero conjugations remain in the Model transformation used by realization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
      CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex

/-- The unitor identifies the actual tensor multiplication with the same objectwise scalar. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterTensorModelUnit.lean:28"
  "adaptation" "Original tensor unitor scalar and both selected-zero conjugations."]
theorem tensorAutomorphism_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) (K : (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory) :
    (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom.app K =
      (boundedAboveFlatPerfectGlobalUnitIso X r).hom.app
        ((boundedAboveFlatPerfectTensorUnitPullback f).obj K) := by
  have hp : (boundedAboveFlatPerfectPullbackUnitIso f r).hom.app K =
      (boundedAboveFlatPerfectGlobalUnitIso X r).hom.app
        ((boundedAboveFlatPerfectPullback f).obj K) := by
    simp only [boundedAboveFlatPerfectPullbackUnitIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app,
      Category.id_comp]
    exact Category.comp_id _
  apply (cancel_mono ((boundedAboveFlatPerfectTensorUnitPullbackIso f).hom.app K)).mp
  have h := NatTrans.congr_app
    (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism_unitor f r) K
  simp only [NatTrans.comp_app] at h
  rw [h, hp]
  exact (boundedAboveFlatPerfectGlobalUnitIso X r).hom.naturality
    ((boundedAboveFlatPerfectTensorUnitPullbackIso f).hom.app K)

local instance parameterTensorModelUnitDownEquivalence {X : Scheme.{u}} :
    (AsSmall.down : AsSmall.{0} ((boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory) ⥤
      (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory).IsEquivalence :=
  (AsSmall.equiv : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory ≌
    AsSmall.{0} ((boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory)).isEquivalence_inverse

/-- The fixed raw rebase retains the original genuine tensor automorphism. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterTensorModelUnit.lean:56"
  "adaptation" "Original tensor unitor scalar and both selected-zero conjugations."]
theorem tensorModelTransformation_scalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    tensorUnitPullbackModelTransformation f r =
      (onFunctor (tensorUnitPullbackModelMap f).hom.toFunctor
        (evaluationSmallUnit (op X) r)).hom := by
  apply NatTrans.ext
  funext K
  change AsSmall.{0} ((boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory) at K
  apply (AsSmall.down : AsSmall.{0} ((boundedAboveFlatPerfectComplex
      X.toRingedSpace).FullSubcategory) ⥤
    (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory).map_injective
  rw [onFunctor_hom_app, evaluationSmallUnit, map_lift_hom]
  simp only [tensorUnitPullbackModelTransformation, whiskerLeft_app, whiskerRight_app,
    AsSmall.down_map, AsSmall.up_map_down, normalizedWeakTransformation, NatTrans.comp_app]
  rw [tensorAutomorphism_scalar]
  let p := boundedAboveFlatPerfectTensorUnitPullback f
  let h := boundedAboveFlatPerfectTensorUnitPullback_exact f
  let q := CategoryTheory.rebaseFunctor p
    (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).zero (boundedAboveFlatPerfectWaldhausen
      X.toRingedSpace).zero
    ((h.zero (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).isZero).iso
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).isZero)
  let z : p ≅ q := CategoryTheory.rebaseFunctorIso _ _ _ _
  have hn := (boundedAboveFlatPerfectGlobalUnitIso X r).hom.naturality
    (z.hom.app (AsSmall.down.obj K))
  simp only [Functor.id_map, Functor.id_obj] at hn
  change z.inv.app (AsSmall.down.obj K) ≫
      (boundedAboveFlatPerfectGlobalUnitIso X r).hom.app (p.obj (AsSmall.down.obj K)) ≫
      z.hom.app (AsSmall.down.obj K) =
    (boundedAboveFlatPerfectGlobalUnitIso X r).hom.app (q.obj (AsSmall.down.obj K))
  rw [← hn, Iso.inv_hom_id_app_assoc]

/-- The complete Model comparison intertwines the original internal and tensor units. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterTensorModelUnit.lean:87"
  "adaptation" "Original tensor unitor scalar and both selected-zero conjugations."]
theorem internalTensorModelIso_unit (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    whiskerRight
      (onFunctor (boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q
      X).op).hom.toFunctor
        (boundedAboveFlatGlobalSectionUnit (op (scheme Q (laurent.op.obj X)))
          (ParameterLaurentUnit.projectedLaurentScalar Q X))).hom
      (evaluationModel (op (scheme Q (laurent.op.obj X)))).hom.toFunctor ≫
      (internalTensorModelIso Q X).hom =
    (internalTensorModelIso Q X).hom ≫
      whiskerLeft (evaluationModel (op (scheme Q X))).hom.toFunctor
        (tensorUnitPullbackModelTransformation (coefficientMap Q X)
          (ParameterLaurentUnit.projectedLaurentScalar Q X)) := by
  rw [tensorModelTransformation_scalar]
  exact onFunctor_whisker_square (boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q
      X).op).hom.toFunctor
    (tensorUnitPullbackModelMap (coefficientMap Q X)).hom.toFunctor
    (evaluationModel (op (scheme Q X))).hom.toFunctor
    (evaluationModel (op (scheme Q (laurent.op.obj X)))).hom.toFunctor
    (internalTensorModelIso Q X).hom
    (boundedAboveFlatGlobalSectionUnit (op (scheme Q (laurent.op.obj X)))
      (ParameterLaurentUnit.projectedLaurentScalar Q X))
    (evaluationSmallUnit (op (scheme Q (laurent.op.obj X)))
      (ParameterLaurentUnit.projectedLaurentScalar Q X))
    (evaluationModel_unit (op (scheme Q (laurent.op.obj X)))
      (ParameterLaurentUnit.projectedLaurentScalar Q X)).whisker

end AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow

namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow

attribute [colib_tag "COL-0547"] internalTensorModelIso_unit

end AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
