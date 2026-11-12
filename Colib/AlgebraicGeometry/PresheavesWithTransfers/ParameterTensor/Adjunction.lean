/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterFunctor
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor.Desc
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor.Unit
public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The tensor and parameter-section adjunction

The ordinary unit takes the pure tensor with the original identity
correspondence. Its inverse in the adjunction evaluates the actual
correspondence action on each pure tensor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]


/-- A map of transfer presheaves from the coend is determined by the pure tensors. -/
theorem parameterTensorPresheaf_hom_ext (F : Cor k ⥤ Cor k)
    {P Q : PresheafWithTransfers.{u + 1} k}
    {f g : parameterTensorPresheaf F P ⟶ Q}
    (h : ∀ (X Y : Cor k) (s : sections P Y) (a : X ⟶ F.obj Y),
      f.hom.app (op X) (parameterTensorGenerator F P X Y s a) =
        g.hom.app (op X) (parameterTensorGenerator F P X Y s a)) : f = g := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  let U := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  let M := parameterTensorSections F P X.unop
  let N := ModuleCat.of ℤ (sections Q X.unop)
  let φ : U.obj M ⟶ U.obj N := f.hom.app X
  let ψ : U.obj M ⟶ U.obj N := g.hom.app X
  have hfg : U.preimage φ = U.preimage ψ := by
    apply parameterTensorSections_hom_ext
    intro Y s a
    let z := parameterTensorGenerator F P X.unop Y s a
    exact (ConcreteCategory.congr_hom (U.map_preimage φ) z).trans
      ((h X.unop Y s a).trans (ConcreteCategory.congr_hom (U.map_preimage ψ) z).symm)
  change φ = ψ
  rw [← U.map_preimage φ, ← U.map_preimage ψ, hfg]

variable (T : SmoothSite (Spec (.of k))) [GeometricallyIntegral T.hom]

local notation "F" => Cor.parameterProduct T

/-- The adjunction bijection, with the specified transfer and unit formulas. -/
def parameterTensorHomEquiv (P Q : (PresheafWithTransfers.{u + 1} k)) :
    (parameterTensorPresheaf F P ⟶ Q) ≃ (P ⟶ withParameter Q T) where
  toFun f := parameterTensorUnit T P ≫ withParameterMap f T
  invFun := parameterTensorDesc T
  left_inv f := by
    apply parameterTensorPresheaf_hom_ext
    intro X Y s a
    rw [parameterTensorDesc_app_generator]
    let z := parameterTensorGenerator F P ((F).obj Y) Y s (𝟙 _)
    change transfer Q a (f.hom.app (op ((F).obj Y)) z) =
      f.hom.app (op X) (parameterTensorGenerator F P X Y s a)
    have h := ConcreteCategory.congr_hom (transfer_naturality f a) z
    change f.hom.app (op X) (parameterTensorTransfer F P a z) =
      transfer Q a (f.hom.app (op ((F).obj Y)) z) at h
    rw [show z = parameterTensorGenerator F P ((F).obj Y) Y s (𝟙 _) from rfl,
      parameterTensorTransfer_generator, Category.comp_id] at h
    exact h.symm
  right_inv θ := by
    apply ObjectProperty.hom_ext
    ext X s
    change (parameterTensorDesc T θ).hom.app (op ((F).obj X.unop))
      (parameterTensorGenerator F P ((F).obj X.unop) X.unop s (𝟙 _)) = θ.hom.app X s
    rw [parameterTensorDesc_app_generator, transfer_id]
    rfl

/-- The parameter adjunction acts by the original coefficient maps on the right. -/
theorem parameterTensorHomEquiv_naturality_right (P Q Q' : PresheafWithTransfers.{u + 1} k)
    (g : Q ⟶ Q') (f : parameterTensorPresheaf F P ⟶ Q) :
    parameterTensorHomEquiv T P Q' (f ≫ g) =
      parameterTensorHomEquiv T P Q f ≫
        (withParameterFunctor T :
          PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k).map g := by
  let R : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k :=
    withParameterFunctor T
  let η : P ⟶ R.obj (parameterTensorPresheaf F P) := parameterTensorUnit T P
  change η ≫ R.map (f ≫ g) = (η ≫ R.map f) ≫ R.map g
  exact (congrArg (fun h => η ≫ h) (R.map_comp f g)).trans
    (Category.assoc η (R.map f) (R.map g)).symm

/-- Tensoring with the parameter is left adjoint to its original section functor. -/
def parameterTensorFunctor : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k :=
  Adjunction.leftAdjointOfEquiv
    (G := (withParameterFunctor T :
      PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k))
    (F_obj := parameterTensorPresheaf F) (parameterTensorHomEquiv T)
    (parameterTensorHomEquiv_naturality_right T)

/-- The adjunction on the original transfer categories. -/
def parameterTensorAdjunction :
    parameterTensorFunctor T ⊣ (withParameterFunctor T :
      PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k) :=
  Adjunction.adjunctionOfEquivLeft
    (G := (withParameterFunctor T :
      PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k))
    (F_obj := parameterTensorPresheaf F) (parameterTensorHomEquiv T)
    (parameterTensorHomEquiv_naturality_right T)

instance : (parameterTensorFunctor T).IsLeftAdjoint :=
  (parameterTensorAdjunction T).isLeftAdjoint

instance : (parameterTensorFunctor T).Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (parameterTensorFunctor T)
  exact Functor.additive_of_preservesBinaryBiproducts (parameterTensorFunctor T)

/-- The actual adjunction unit is the original pure-tensor map. -/
@[simp]
theorem parameterTensorAdjunction_unit_app (P : PresheafWithTransfers.{u + 1} k) :
    (parameterTensorAdjunction T).unit.app P = parameterTensorUnit T P := by
  let R : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k :=
    withParameterFunctor T
  let η : P ⟶ R.obj (parameterTensorPresheaf F P) := parameterTensorUnit T P
  change η ≫ R.map (𝟙 (parameterTensorPresheaf F P)) = η
  rw [R.map_id, Category.comp_id]

end AlgebraicGeometry.PresheafWithTransfers
