/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor.Reduced
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor.Representable
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation

/-!
# The reduced tensor of a transfer representable

The unit mate sends the coend generators to postcomposition with the
original unit graph. The actual tensor quotient is therefore the
target-unit quotient used in the cancellation map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "Bₖ" => SmoothSite.base (Spec (CommRingCat.of k))
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "F₀" => Cor.parameterProduct Bₖ
local notation "F₁" => Cor.parameterProduct Gₘ
local notation "r(" Y ")" => Functor.obj (representableLarge k) Y

/-- The unit mate on the tensor representable is postcomposition with
the actual unit correspondence. -/
@[reassoc]
theorem torusParameterTensorUnit_representable (Y : Cor k) :
    (torusParameterTensorUnit k).app (r(Y)) ≫ (parameterTensorRepresentableIso Gₘ Y).hom =
      (parameterTensorRepresentableIso Bₖ Y).hom ≫
        (representableLarge k).map (torusUnitCorrespondence k Y) := by
  let a := parameterTensorAdjunction Bₖ
  let b := parameterTensorAdjunction Gₘ
  let e := (parameterTensorRepresentableIso Bₖ Y).hom
  let d := (parameterTensorRepresentableIso Gₘ Y).hom
  let f := (representableLarge k).map (torusUnitCorrespondence k Y)
  apply (a.homEquiv _ _).injective
  rw [torusParameterTensorUnit_homEquiv k, Adjunction.homEquiv_naturality_right]
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro s
  obtain ⟨α⟩ := s
  let X := V.unop
  have h₀ : ((a.homEquiv _ _) e).hom.app V (ULift.up α) = ULift.up ((F₀).map α) := by
    rw [Adjunction.homEquiv_unit]
    exact parameterTensorRepresentable_unit_app Bₖ Y X α
  have h₁ : ((b.homEquiv _ _) d).hom.app V (ULift.up α) = ULift.up ((F₁).map α) := by
    rw [Adjunction.homEquiv_unit]
    exact parameterTensorRepresentable_unit_app Gₘ Y X α
  change (torusUnit (r((F₁).obj Y))).hom.app (op X)
      (((b.homEquiv _ _) d).hom.app V (ULift.up α)) =
    f.hom.app (op ((F₀).obj X)) (((a.homEquiv _ _) e).hom.app V (ULift.up α))
  rw [h₀, h₁]
  change ULift.up (torusUnitCorrespondence k X ≫ (F₁).map α) =
    f.hom.app (op ((F₀).obj X)) (ULift.up ((F₀).map α))
  rw [representableLarge_map_app_apply]
  exact congrArg ULift.up
    ((Cor.parameterProductMap (SmoothSite.torusOne (Spec (.of k)))).naturality α).symm

/-- The actual reduced tensor of a representable is its original
target-unit quotient. -/
@[no_expose]
def reducedParameterTensorRepresentableIso (Y : Cor k) :
    (reducedParameterTensorFunctor k).obj (r(Y)) ≅ torusCancellationCoefficients k Y := by
  unfold reducedParameterTensorFunctor
  exact cokernel.mapIso ((torusParameterTensorUnit k).app (r(Y)))
    ((representableLarge k).map (torusUnitCorrespondence k Y))
    (parameterTensorRepresentableIso Bₖ Y) (parameterTensorRepresentableIso Gₘ Y)
    (torusParameterTensorUnit_representable k Y)

/-- The representable comparison retains the original quotient map. -/
@[reassoc]
theorem reducedParameterTensorRepresentableIso_quotient (Y : Cor k) :
    (reducedParameterTensorQuotient k).app (r(Y)) ≫
        (reducedParameterTensorRepresentableIso k Y).hom =
      (parameterTensorRepresentableIso Gₘ Y).hom ≫ toTorusCancellationCoefficients k Y := by
  rw [reducedParameterTensorQuotient_app]
  unfold reducedParameterTensorRepresentableIso
  exact cokernel.π_desc ((torusParameterTensorUnit k).app (r(Y))) _ _

/-- The same quotient comparison on the original cochain complex in
degree `n`. -/
def reducedParameterTensorSingleRepresentableIso (Y : Cor k) (n : ℤ) :
    ((reducedParameterTensorFunctor k).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor (PresheafWithTransfers.{u + 1} k) n).obj (r(Y))) ≅
      (CochainComplex.singleFunctor (PresheafWithTransfers.{u + 1} k) n).obj
        (torusCancellationCoefficients k Y) :=
  (HomologicalComplex.singleMapHomologicalComplex (reducedParameterTensorFunctor k)
    (.up ℤ) n).app (r(Y)) ≪≫
      (CochainComplex.singleFunctor _ n).mapIso (reducedParameterTensorRepresentableIso k Y)

/-- The original quotient on a placed representable is obtained by
placing the actual target-unit quotient. -/
@[reassoc]
theorem reducedParameterTensorSingleRepresentableIso_quotient (Y : Cor k) (n : ℤ) :
    ((reducedParameterTensorQuotient k).mapHomologicalComplex (.up ℤ)).app
        ((CochainComplex.singleFunctor (PresheafWithTransfers.{u + 1} k) n).obj (r(Y))) ≫
      (reducedParameterTensorSingleRepresentableIso k Y n).hom =
    (HomologicalComplex.singleMapHomologicalComplex (parameterTensorFunctor Gₘ) (.up ℤ)
      n).hom.app (r(Y)) ≫ (CochainComplex.singleFunctor _ n).map
        ((parameterTensorRepresentableIso Gₘ Y).hom ≫ toTorusCancellationCoefficients k Y) := by
  let C := PresheafWithTransfers.{u + 1} k
  let S := CochainComplex.singleFunctor C n
  let L := parameterTensorFunctor Gₘ
  let R := reducedParameterTensorFunctor k
  let q := reducedParameterTensorQuotient k
  let P := (representableLarge k).obj Y
  let e := (HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) n).hom.app P
  let d := (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) n).hom.app P
  let a := (reducedParameterTensorRepresentableIso k Y).hom
  let p := (parameterTensorRepresentableIso Gₘ Y).hom ≫ toTorusCancellationCoefficients k Y
  have h : ((q.mapHomologicalComplex (.up ℤ)).app (S.obj P)) ≫ d = e ≫ S.map (q.app P) := by
    let j := (HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) n).app P
    have hq := HomologicalComplex.natTransMapHomologicalComplex_app_single_obj_assoc
      q (.up ℤ) n P d
    change ((q.mapHomologicalComplex (.up ℤ)).app (S.obj P)) ≫ d =
      e ≫ S.map (q.app P) ≫ j.inv ≫ j.hom at hq
    exact hq.trans ((congrArg (e ≫ S.map (q.app P) ≫ ·) j.inv_hom_id).trans
      ((Category.assoc _ _ _).symm.trans (Category.comp_id _)))
  change ((q.mapHomologicalComplex (.up ℤ)).app (S.obj P)) ≫ (d ≫ S.map a) = e ≫ S.map p
  calc
    _ = (e ≫ S.map (q.app P)) ≫ S.map a := (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ S.map a) h)
    _ = e ≫ S.map (q.app P ≫ a) := (Category.assoc _ _ _).trans
      (congrArg (e ≫ ·) (S.map_comp _ _).symm)
    _ = _ := congrArg (fun f => e ≫ S.map f) (reducedParameterTensorRepresentableIso_quotient k Y)

end AlgebraicGeometry.PresheafWithTransfers
