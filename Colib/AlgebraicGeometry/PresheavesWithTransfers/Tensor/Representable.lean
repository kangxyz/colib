/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.Pushforward
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.YonedaLarge

/-!
# Additive coend pushforward of representables

The coend of a representable is represented by the image of its representing
object. On each generator the comparison composes the signed correspondence
with the actual image of the representing arrow.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]
variable (F : Cor k ⥤ Cor k) [F.Additive]

local notation "R(" K ", " X ")" => Functor.obj (representableLarge K) X

/-- The comparison induced by the identity correspondence on the parameter product. -/
def coendPushforwardRepresentableHom (X : Cor k) :
    parameterTensorPresheaf F (R(k, X)) ⟶ R(k, (F).obj X) :=
  coendPushforwardDesc F
    (sectionHomLarge ((additivePrecompose F).obj (R(k, (F).obj X))) X (ULift.up (𝟙 ((F).obj X))))

/-- The comparison composes with the original exterior image of the representing arrow. -/
theorem coendPushforwardRepresentableHom_app (X U Y : Cor k) (b : Y ⟶ X)
    (a : U ⟶ (F).obj Y) :
    (coendPushforwardRepresentableHom F X).hom.app (op U)
      (parameterTensorGenerator F (R(k, X)) U Y (ULift.up b) a) =
        ULift.up (a ≫ (F).map b) := by
  let Q := R(k, (F).obj X)
  let θ := sectionHomLarge ((additivePrecompose F).obj Q) X (ULift.up (𝟙 ((F).obj X)))
  have h := coendPushforwardDesc_app_generator F θ U Y (ULift.up b) a
  change (coendPushforwardRepresentableHom F X).hom.app (op U)
    (parameterTensorGenerator F (R(k, X)) U Y (ULift.up b) a) =
      (ULift.up (a ≫ ((F).map b ≫ 𝟙 _)) : ULift.{u + 1} (U ⟶ (F).obj X)) at h
  exact h.trans (congrArg (fun g : (F).obj Y ⟶ (F).obj X => ULift.up (a ≫ g))
    (Category.comp_id ((F).map b)))

/-- The inverse is the coend generator using the original representing diagonal. -/
def coendPushforwardRepresentableInv (X : Cor k) :
    R(k, (F).obj X) ⟶ parameterTensorPresheaf F (R(k, X)) :=
  sectionHomLarge _ ((F).obj X)
    (parameterTensorGenerator F (R(k, X)) ((F).obj X) X (ULift.up (𝟙 X)) (𝟙 _))

omit [F.Additive] in
theorem coendPushforwardRepresentableInv_app (X U : Cor k) (a : U ⟶ (F).obj X) :
    (coendPushforwardRepresentableInv F X).hom.app (op U) (ULift.up a) =
      parameterTensorGenerator F (R(k, X)) U X (ULift.up (𝟙 X)) a := by
  change parameterTensorTransfer F (R(k, X)) a
    (parameterTensorGenerator F (R(k, X)) ((F).obj X) X (ULift.up (𝟙 X)) (𝟙 _)) = _
  exact (parameterTensorTransfer_generator F (R(k, X)) a X (ULift.up (𝟙 X)) (𝟙 _)).trans
    (congrArg (parameterTensorGenerator F (R(k, X)) U X (ULift.up (𝟙 X))) (Category.comp_id a))

/-- The left adjoint sends the actual representable to the parameter-product representable. -/
def coendPushforwardRepresentableIso (X : Cor k) :
    (coendPushforward F).obj (R(k, X)) ≅ R(k, (F).obj X) where
  hom := coendPushforwardRepresentableHom F X
  inv := coendPushforwardRepresentableInv F X
  hom_inv_id := by
    apply parameterTensorPresheaf_hom_ext
    intro U Y s a
    change ULift.{u + 1} (Y ⟶ X) at s
    obtain ⟨b⟩ := s
    change (coendPushforwardRepresentableInv F X).hom.app (op U)
        ((coendPushforwardRepresentableHom F X).hom.app (op U)
          (parameterTensorGenerator F (R(k, X)) U Y (ULift.up b) a)) =
      parameterTensorGenerator F (R(k, X)) U Y (ULift.up b) a
    have h := parameterTensorGenerator_transfer F (R(k, X)) b (ULift.up (𝟙 X)) a
    change parameterTensorGenerator F (R(k, X)) U Y (ULift.up (b ≫ 𝟙 X)) a =
      parameterTensorGenerator F (R(k, X)) U X (ULift.up (𝟙 X)) (a ≫ (F).map b) at h
    rw [Category.comp_id] at h
    have h₁ := coendPushforwardRepresentableHom_app F X U Y b a
    have h₂ := coendPushforwardRepresentableInv_app F X U (a ≫ (F).map b)
    exact (congrArg (fun z : sections (R(k, (F).obj X)) U =>
      (coendPushforwardRepresentableInv F X).hom.app (op U) z) h₁).trans (h₂.trans h.symm)
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    ext U s
    change ULift.{u + 1} (U.unop ⟶ (F).obj X) at s
    obtain ⟨a⟩ := s
    change (coendPushforwardRepresentableHom F X).hom.app (op U.unop)
      ((coendPushforwardRepresentableInv F X).hom.app (op U.unop) (ULift.up a)) = ULift.up a
    have h₁ := coendPushforwardRepresentableInv_app F X U.unop a
    have h₂ := coendPushforwardRepresentableHom_app F X U.unop X (𝟙 X) a
    have h₃ : a ≫ (F).map (𝟙 X) = a :=
      (congrArg (fun f => a ≫ f) ((F).map_id X)).trans (Category.comp_id a)
    exact (congrArg (fun z => (coendPushforwardRepresentableHom F X).hom.app (op U.unop) z)
      h₁).trans (h₂.trans (congrArg ULift.up h₃))

/-- A map of coefficients acts by applying it to the section in the original pure generator. -/
theorem coendPushforward_map_generator {P Q : PresheafWithTransfers.{u + 1} k}
    (f : P ⟶ Q) (U Y : Cor k) (s : sections P Y) (a : U ⟶ F.obj Y) :
    ((coendPushforward F).map f).hom.app (op U)
      (parameterTensorGenerator F P U Y s a) =
    parameterTensorGenerator F Q U Y (f.hom.app (op Y) s) a := by
  let V := additivePrecompose F
  have hm : (coendPushforward F).map f =
      coendPushforwardDesc F (f ≫ coendPushforwardUnit F Q) := by
    change coendPushforwardDesc F (f ≫ coendPushforwardUnit F Q ≫ V.map (𝟙 _)) =
      coendPushforwardDesc F (f ≫ coendPushforwardUnit F Q)
    rw [V.map_id, Category.comp_id]
  rw [hm]
  change (coendPushforwardDesc F (f ≫ coendPushforwardUnit F Q)).hom.app (op U)
      (parameterTensorGenerator F P U Y s a) = _
  rw [coendPushforwardDesc_app_generator]
  change parameterTensorTransfer F Q a
    (parameterTensorGenerator F Q (F.obj Y) Y (f.hom.app (op Y) s) (𝟙 _)) = _
  exact (parameterTensorTransfer_generator F Q a Y (f.hom.app (op Y) s) (𝟙 _)).trans
    (congrArg (parameterTensorGenerator F Q U Y (f.hom.app (op Y) s)) (Category.comp_id a))

/-- The representing comparison preserves the image of the original signed arrow. -/
theorem coendPushforwardRepresentableIso_naturality {X Y : Cor k} (f : X ⟶ Y) :
    (coendPushforward F).map ((representableLarge k).map f) ≫
        (coendPushforwardRepresentableIso F Y).hom =
      (coendPushforwardRepresentableIso F X).hom ≫ (representableLarge k).map (F.map f) := by
  apply parameterTensorPresheaf_hom_ext
  intro U V s a
  change ULift.{u + 1} (V ⟶ X) at s
  obtain ⟨b⟩ := s
  let m := (coendPushforward F).map ((representableLarge k).map f)
  let h := coendPushforwardRepresentableHom F X
  let h' := coendPushforwardRepresentableHom F Y
  let g := (representableLarge k).map (F.map f)
  let z := parameterTensorGenerator F (R(k, X)) U V (ULift.up b) a
  change h'.hom.app (op U) (m.hom.app (op U) z) = g.hom.app (op U) (h.hom.app (op U) z)
  have h₁ : m.hom.app (op U) z =
      parameterTensorGenerator F (R(k, Y)) U V (ULift.up (b ≫ f)) a :=
    coendPushforward_map_generator F ((representableLarge k).map f) U V (ULift.up b) a
  have h₂ := coendPushforwardRepresentableHom_app F Y U V (b ≫ f) a
  have h₃ := coendPushforwardRepresentableHom_app F X U V b a
  have h₄ := representableLarge_map_app_apply k (F.map f) (a ≫ F.map b)
  have hh : a ≫ F.map (b ≫ f) = (a ≫ F.map b) ≫ F.map f := by
    rw [F.map_comp, Category.assoc]
  exact (congrArg (h'.hom.app (op U)) h₁).trans
    (h₂.trans ((congrArg ULift.up hh).trans
      (h₄.symm.trans (congrArg (g.hom.app (op U)) h₃).symm)))

/-- The unit on a representable is exterior product on the original signed arrow. -/
theorem coendPushforwardRepresentable_unit_app (X U : Cor k) (b : U ⟶ X) :
    (coendPushforwardRepresentableHom F X).hom.app (op ((F).obj U))
      (((coendPushforwardAdjunction F).unit.app (R(k, X))).hom.app (op U) (ULift.up b)) =
        ULift.up ((F).map b) := by
  rw [coendPushforwardAdjunction_unit_app]
  have h := coendPushforwardUnit_app_apply F (R(k, X)) U (ULift.up b)
  exact (congrArg (fun z => (coendPushforwardRepresentableHom F X).hom.app (op ((F).obj U)) z)
    h).trans ((coendPushforwardRepresentableHom_app F X ((F).obj U) U b (𝟙 _)).trans
      (congrArg ULift.up (Category.id_comp ((F).map b))))

end AlgebraicGeometry.PresheafWithTransfers
