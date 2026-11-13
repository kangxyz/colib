/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor.Adjunction
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.YonedaLarge

/-!
# The parameter tensor of an actual representable

The coend of a representable is represented by the original parameter
product. On each generator the comparison composes the signed correspondence
with the actual exterior image of the representing arrow.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]
variable (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

local notation "F" => Cor.parameterProduct T
local notation "R(" X ")" => Functor.obj (representableLarge k) X

/-- The comparison induced by the identity correspondence on the parameter product. -/
def parameterTensorRepresentableHom (X : Cor k) :
    parameterTensorPresheaf F (R(X)) ⟶ R((F).obj X) :=
  parameterTensorDesc T
    (sectionHomLarge (withParameter (R((F).obj X)) T) X (ULift.up (𝟙 ((F).obj X))))

/-- The comparison composes with the original exterior image of the representing arrow. -/
theorem parameterTensorRepresentableHom_app (X U Y : Cor k) (b : Y ⟶ X)
    (a : U ⟶ (F).obj Y) :
    (parameterTensorRepresentableHom T X).hom.app (op U)
      (parameterTensorGenerator F (R(X)) U Y (ULift.up b) a) =
        ULift.up (a ≫ (F).map b) := by
  let Q := R((F).obj X)
  let θ := sectionHomLarge (withParameter Q T) X (ULift.up (𝟙 ((F).obj X)))
  have h := parameterTensorDesc_app_generator T θ U Y (ULift.up b) a
  change (parameterTensorRepresentableHom T X).hom.app (op U)
    (parameterTensorGenerator F (R(X)) U Y (ULift.up b) a) =
      (ULift.up (a ≫ ((F).map b ≫ 𝟙 _)) : ULift.{u + 1} (U ⟶ (F).obj X)) at h
  exact h.trans (congrArg (fun g : (F).obj Y ⟶ (F).obj X => ULift.up (a ≫ g))
    (Category.comp_id ((F).map b)))

/-- The inverse is the coend generator using the original representing diagonal. -/
def parameterTensorRepresentableInv (X : Cor k) :
    R((F).obj X) ⟶ parameterTensorPresheaf F (R(X)) :=
  sectionHomLarge _ ((F).obj X)
    (parameterTensorGenerator F (R(X)) ((F).obj X) X (ULift.up (𝟙 X)) (𝟙 _))

theorem parameterTensorRepresentableInv_app (X U : Cor k) (a : U ⟶ (F).obj X) :
    (parameterTensorRepresentableInv T X).hom.app (op U) (ULift.up a) =
      parameterTensorGenerator F (R(X)) U X (ULift.up (𝟙 X)) a := by
  change parameterTensorTransfer F (R(X)) a
    (parameterTensorGenerator F (R(X)) ((F).obj X) X (ULift.up (𝟙 X)) (𝟙 _)) = _
  exact (parameterTensorTransfer_generator F (R(X)) a X (ULift.up (𝟙 X)) (𝟙 _)).trans
    (congrArg (parameterTensorGenerator F (R(X)) U X (ULift.up (𝟙 X))) (Category.comp_id a))

/-- The left adjoint sends the actual representable to the parameter-product representable. -/
def parameterTensorRepresentableIso (X : Cor k) :
    (parameterTensorFunctor T).obj (R(X)) ≅ R((F).obj X) where
  hom := parameterTensorRepresentableHom T X
  inv := parameterTensorRepresentableInv T X
  hom_inv_id := by
    apply parameterTensorPresheaf_hom_ext
    intro U Y s a
    change ULift.{u + 1} (Y ⟶ X) at s
    obtain ⟨b⟩ := s
    change (parameterTensorRepresentableInv T X).hom.app (op U)
        ((parameterTensorRepresentableHom T X).hom.app (op U)
          (parameterTensorGenerator F (R(X)) U Y (ULift.up b) a)) =
      parameterTensorGenerator F (R(X)) U Y (ULift.up b) a
    have h := parameterTensorGenerator_transfer F (R(X)) b (ULift.up (𝟙 X)) a
    change parameterTensorGenerator F (R(X)) U Y (ULift.up (b ≫ 𝟙 X)) a =
      parameterTensorGenerator F (R(X)) U X (ULift.up (𝟙 X)) (a ≫ (F).map b) at h
    rw [Category.comp_id] at h
    have h₁ := parameterTensorRepresentableHom_app T X U Y b a
    have h₂ := parameterTensorRepresentableInv_app T X U (a ≫ (F).map b)
    exact (congrArg (fun z : sections (R((F).obj X)) U =>
      (parameterTensorRepresentableInv T X).hom.app (op U) z) h₁).trans (h₂.trans h.symm)
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    ext U s
    change ULift.{u + 1} (U.unop ⟶ (F).obj X) at s
    obtain ⟨a⟩ := s
    change (parameterTensorRepresentableHom T X).hom.app (op U.unop)
      ((parameterTensorRepresentableInv T X).hom.app (op U.unop) (ULift.up a)) = ULift.up a
    have h₁ := parameterTensorRepresentableInv_app T X U.unop a
    have h₂ := parameterTensorRepresentableHom_app T X U.unop X (𝟙 X) a
    have h₃ : a ≫ (F).map (𝟙 X) = a :=
      (congrArg (fun f => a ≫ f) ((F).map_id X)).trans (Category.comp_id a)
    exact (congrArg (fun z => (parameterTensorRepresentableHom T X).hom.app (op U.unop) z)
      h₁).trans (h₂.trans (congrArg ULift.up h₃))

/-- The unit on a representable is exterior product on the original signed arrow. -/
theorem parameterTensorRepresentable_unit_app (X U : Cor k) (b : U ⟶ X) :
    (parameterTensorRepresentableHom T X).hom.app (op ((F).obj U))
      (((parameterTensorAdjunction T).unit.app (R(X))).hom.app (op U) (ULift.up b)) =
        ULift.up ((F).map b) := by
  rw [parameterTensorAdjunction_unit_app]
  have h := parameterTensorUnit_app_apply T (R(X)) U (ULift.up b)
  exact (congrArg (fun z => (parameterTensorRepresentableHom T X).hom.app (op ((F).obj U)) z)
    h).trans ((parameterTensorRepresentableHom_app T X ((F).obj U) U b (𝟙 _)).trans
      (congrArg ULift.up (Category.id_comp ((F).map b))))

end AlgebraicGeometry.PresheafWithTransfers
