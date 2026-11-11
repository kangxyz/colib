/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorRowPasting
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationInverseModel

/-!
# Returning the genuine parameter tensor row through actual evaluation

The genuine tensor Model map is followed by the exact, chosen-zero-normalized
categorical evaluation inverse. The original unit of that equivalence and the
full tensor/evaluation comparison give a real endpoint path in the original
global Model. Its unit-intertwining square retains the genuine tensor multiplication.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex

/-- Return an actual functor isomorphism through the specified categorical unit. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorReturnedModel.lean:32"
  "adaptation" "Original returned actual tensor row via the exact categorical inverse"]
def returnIso {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (A : D ⥤ E) (B : E ⥤ D) (G : C ⥤ E)
    (j : A ⋙ B ≅ 𝟭 D) (e : F ⋙ A ≅ G) : F ≅ G ⋙ B :=
  (Functor.rightUnitor F).symm ≪≫ isoWhiskerLeft F j.symm ≪≫
    (Functor.associator F A B).symm ≪≫ isoWhiskerRight e B

/-- The specified categorical unit transports an actual whole transformation square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorReturnedModel.lean:39"
  "adaptation" "Original returned actual tensor row via the exact categorical inverse"]
theorem returnIso_intertwining
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C ⥤ D) (A : D ⥤ E) (B : E ⥤ D) (G : C ⥤ E)
    (j : A ⋙ B ≅ 𝟭 D) (e : F ⋙ A ≅ G)
    (η : F ⟶ F) (θ : G ⟶ G)
    (h : whiskerRight η A ≫ e.hom = e.hom ≫ θ) :
    η ≫ (returnIso F A B G j e).hom =
      (returnIso F A B G j e).hom ≫ whiskerRight θ B := by
  apply NatTrans.ext
  funext X
  have he := congrArg (fun t => B.map (t.app X)) h
  have hj := j.inv.naturality (η.app X)
  simp only [NatTrans.comp_app, whiskerRight_app, Functor.map_comp] at he
  simp only [Functor.id_map, Functor.comp_map] at hj
  simp only [returnIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Functor.rightUnitor_inv_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.id_comp]
  rw [← Category.assoc, hj, Category.assoc, he, ← Category.assoc]

/-- The genuine tensor functor returns to the original target through the actual exact inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorReturnedModel.lean:60"
  "adaptation" "Original returned actual tensor row via the exact categorical inverse"]
def returnedTensorModel (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  tensorModelMap Q X ≫ evaluationInverseModel (op (scheme Q (laurent.op.obj X)))

/-- The original unit and tensor comparison give the full moving endpoint in the global Model. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorReturnedModel.lean:64"
  "adaptation" "Original returned actual tensor row via the exact categorical inverse"]
def returnedTensorIso (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q X).op).hom.toFunctor ≅
      (returnedTensorModel Q X).hom.toFunctor :=
  returnIso (boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q X).op).hom.toFunctor
    (evaluationModel (op (scheme Q (laurent.op.obj X)))).hom.toFunctor
    (evaluationInverseModel (op (scheme Q (laurent.op.obj X)))).hom.toFunctor
    (tensorModelMap Q X).hom.toFunctor
    (evaluationInverseUnit (op (scheme Q (laurent.op.obj X))))
    (internalTensorModelIso Q X)

/-- The returned transformation is still the original tensor multiplication, under exact functors.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorReturnedModel.lean:75"
  "adaptation" "Original returned actual tensor row via the exact categorical inverse"]
def returnedTensorUnit (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  whiskerRight (tensorModelUnit Q X)
    (evaluationInverseModel (op (scheme Q (laurent.op.obj X)))).hom.toFunctor

/-- Returning the actual tensor/evaluation square preserves its entire natural transformation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterTensorReturnedModel.lean:80"
  "adaptation" "Original returned actual tensor row via the exact categorical inverse"]
theorem returnedTensorIso_unit (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (onFunctor (boundedAboveFlatGlobalSectionModelFunctor.map (coefficientMap Q X).op).hom.toFunctor
      (boundedAboveFlatGlobalSectionUnit (op (scheme Q (laurent.op.obj X)))
        (ParameterLaurentUnit.projectedLaurentScalar Q X))).hom ≫
        (returnedTensorIso Q X).hom =
      (returnedTensorIso Q X).hom ≫ returnedTensorUnit Q X :=
  returnIso_intertwining _ _ _ _ _ _ _ _ (internalTensorModelIso_unit Q X)

end AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow

namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow

attribute [colib_tag "COL-0550"] returnedTensorModel
attribute [colib_tag "COL-0550"] returnedTensorIso_unit

end AlgebraicGeometry.Scheme.Modules.ParameterTensorEvaluationRow
