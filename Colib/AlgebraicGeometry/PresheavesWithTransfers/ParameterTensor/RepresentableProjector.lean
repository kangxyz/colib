/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor.ReducedRepresentable
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.Normalization

/-! # The Laurent projector on the actual transfer representables -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]
variable (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

local notation "R" => representableLarge k

/-- The coend comparison on the original representables is natural for
all signed correspondences. -/
@[reassoc]
theorem parameterTensorRepresentableIso_hom_naturality {X Y : Cor k} (f : X ⟶ Y) :
    (parameterTensorFunctor T).map ((R).map f) ≫ (parameterTensorRepresentableIso T Y).hom =
      (parameterTensorRepresentableIso T X).hom ≫ (R).map ((Cor.parameterProduct T).map f) := by
  let F := Cor.parameterProduct T
  let a := parameterTensorAdjunction T
  apply (a.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨α⟩ := x
  let e := a.homEquiv ((R).obj X) ((R).obj (F.obj X))
    (parameterTensorRepresentableIso T X).hom
  let d := a.homEquiv ((R).obj Y) ((R).obj (F.obj Y))
    (parameterTensorRepresentableIso T Y).hom
  have he : e.hom.app U (ULift.up α) = ULift.up (F.map α) := by
    unfold e
    rw [Adjunction.homEquiv_unit]
    exact parameterTensorRepresentable_unit_app T X U.unop α
  have hd : d.hom.app U (ULift.up (α ≫ f)) = ULift.up (F.map (α ≫ f)) := by
    unfold d
    rw [Adjunction.homEquiv_unit]
    exact parameterTensorRepresentable_unit_app T Y U.unop (α ≫ f)
  change d.hom.app U (ULift.up (α ≫ f)) =
    ((R).map (F.map f)).hom.app (op (F.obj U.unop)) (e.hom.app U (ULift.up α))
  rw [he, hd, representableLarge_map_app_apply, Functor.map_comp]

variable (k)

local notation "S" => Spec (CommRingCat.of k)
local notation "B" => SmoothSite.base S
local notation "G" => SmoothSite.multiplicativeGroupObject S

/-- The constant-section mate on the tensor representable is induced by
the actual projection in the base parameter coordinates. -/
@[reassoc]
theorem torusParameterTensorProjection_representable (Y : Cor k) :
    (torusParameterTensorProjection k).app ((R).obj Y) ≫ (parameterTensorRepresentableIso B Y).hom =
      (parameterTensorRepresentableIso G Y).hom ≫
        (R).map (torusProjectionCorrespondence k Y) := by
  let a := parameterTensorAdjunction G
  let b := parameterTensorAdjunction B
  let e := (parameterTensorRepresentableIso G Y).hom
  let d := (parameterTensorRepresentableIso B Y).hom
  let f := (R).map (torusProjectionCorrespondence k Y)
  apply (a.homEquiv _ _).injective
  rw [torusParameterTensorProjection_homEquiv k, Adjunction.homEquiv_naturality_right]
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro s
  obtain ⟨α⟩ := s
  let X := V.unop
  have h₀ : ((a.homEquiv _ _) e).hom.app V (ULift.up α) =
      ULift.up ((Cor.parameterProduct G).map α) := by
    rw [Adjunction.homEquiv_unit]
    exact parameterTensorRepresentable_unit_app G Y X α
  have h₁ : ((b.homEquiv _ _) d).hom.app V (ULift.up α) =
      ULift.up ((Cor.parameterProduct B).map α) := by
    rw [Adjunction.homEquiv_unit]
    exact parameterTensorRepresentable_unit_app B Y X α
  change (torusConstant ((R).obj ((Cor.parameterProduct B).obj Y))).hom.app V
      (((b.homEquiv _ _) d).hom.app V (ULift.up α)) =
    f.hom.app (op ((Cor.parameterProduct G).obj X)) (((a.homEquiv _ _) e).hom.app V (ULift.up α))
  rw [h₀, h₁]
  change ULift.up (torusProjectionCorrespondence k X ≫ (Cor.parameterProduct B).map α) =
    f.hom.app (op ((Cor.parameterProduct G).obj X)) (ULift.up ((Cor.parameterProduct G).map α))
  rw [representableLarge_map_app_apply]
  exact congrArg ULift.up ((Cor.parameterProductMap (toBase G)).naturality α).symm

/-- On the original Laurent product representable the unreduced projector
is the literal structural projection followed by the unit graph. -/
@[reassoc]
theorem torusParameterTensorProjector_representable (Y : Cor k) :
    ((torusParameterTensorProjection k ≫ torusParameterTensorUnit k).app ((R).obj Y)) ≫
        (parameterTensorRepresentableIso G Y).hom =
      (parameterTensorRepresentableIso G Y).hom ≫ (R).map (torusUnitProjector k Y) := by
  dsimp only [NatTrans.comp_app]
  rw [Category.assoc, torusParameterTensorUnit_representable, ← Category.assoc,
    torusParameterTensorProjection_representable, Category.assoc, ← Functor.map_comp]
  rfl

end AlgebraicGeometry.PresheafWithTransfers
