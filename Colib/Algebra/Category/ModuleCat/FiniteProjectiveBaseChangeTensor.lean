/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeUniversal
public import Colib.Algebra.Category.ModuleCat.RightScalarExtension

/-!
# Literal tensor comparison for finite projective modules

Two universal lifts identify the independently constructed balanced quotient
with the unchanged matrix-image change of rings. The comparison preserves the
actual semilinear unit. Finite generation and projectivity are transported to
the quotient itself, so the tensor functor restricts to finite projectives.

For independently universed rings the natural comparison is made after an
explicit universe lift of the original target. In a common ring universe it is
an isomorphism of the original finite-projective target category.

## Implementation provenance

Adapted from the Quillen source
`Quillen/Aglib/Algebra/Category/ModuleCat/FiniteProjectiveBaseChangeTensor.lean` at revision
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory MulOpposite

namespace ModuleCat.FiniteProjective

open RightScalarExtension

variable {R : Type u} {S : Type v} [Ring R] [Ring S]
variable (f : R →+* S) (P : Category.{u, u} Rᵐᵒᵖ)

/-- The canonical tensor lift of the actual original scalar-extension unit. -/
def tensorToBaseChange : Tensor f P.obj →ₗ[Sᵐᵒᵖ] ((rightBaseChange f).obj P).obj :=
  lift f (rightBaseChangeUnit f P)

/-- The original universal lift of the tensor unit, into the actual quotient. -/
def baseChangeToTensor : ((rightBaseChange f).obj P).obj →ₗ[Sᵐᵒᵖ] Tensor f P.obj :=
  rightBaseChangeLift f P (ModuleCat.of Sᵐᵒᵖ (Tensor f P.obj)) (unit f)

@[simp] theorem tensorToBaseChange_pure (p : P.obj) (s : S) :
    tensorToBaseChange f P (pure f p s) = op s • rightBaseChangeUnit f P p :=
  lift_pure f (rightBaseChangeUnit f P) p s

theorem tensorToBaseChange_unit (p : P.obj) :
    tensorToBaseChange f P (unit f p) = rightBaseChangeUnit f P p :=
  lift_unit f (rightBaseChangeUnit f P) p

@[simp] theorem baseChangeToTensor_unit (p : P.obj) :
    baseChangeToTensor f P (rightBaseChangeUnit f P p) = unit f p :=
  DFunLike.congr_fun
    (rightBaseChangeLift_unit f P (ModuleCat.of Sᵐᵒᵖ (Tensor f P.obj)) (unit f)) p

/-- The two universal lifts are inverse on the unchanged base-change object. -/
theorem tensorToBaseChange_comp_baseChangeToTensor :
    (tensorToBaseChange f P).comp (baseChangeToTensor f P) = LinearMap.id := by
  apply rightBaseChange_hom_ext f P ((rightBaseChange f).obj P).obj
  ext p
  simp

/-- The two universal lifts are inverse on the literal quotient. -/
theorem baseChangeToTensor_comp_tensorToBaseChange :
    (baseChangeToTensor f P).comp (tensorToBaseChange f P) = LinearMap.id := by
  apply hom_ext_unit f
  intro p
  simp

/-- Canonical identification of the literal quotient with original change of rings. -/
def rightTensorBaseChangeEquiv :
    Tensor f P.obj ≃ₗ[Sᵐᵒᵖ] ((rightBaseChange f).obj P).obj :=
  LinearEquiv.ofLinearMap (tensorToBaseChange f P) (baseChangeToTensor f P)
    (tensorToBaseChange_comp_baseChangeToTensor f P)
    (baseChangeToTensor_comp_tensorToBaseChange f P)

@[simp] theorem rightTensorBaseChangeEquiv_pure (p : P.obj) (s : S) :
    rightTensorBaseChangeEquiv f P (pure f p s) = op s • rightBaseChangeUnit f P p :=
  tensorToBaseChange_pure f P p s

theorem rightTensorBaseChangeEquiv_unit (p : P.obj) :
    rightTensorBaseChangeEquiv f P (unit f p) = rightBaseChangeUnit f P p :=
  tensorToBaseChange_unit f P p

/-- Naturality is forced by the original unit and the quotient universal property. -/
theorem rightTensorBaseChangeEquiv_naturality {P Q : Category.{u, u} Rᵐᵒᵖ}
    (a : P ⟶ Q) :
    (rightTensorBaseChangeEquiv f Q).toLinearMap.comp (RightScalarExtension.map f a.hom.hom) =
      ((rightBaseChange f).map a).hom.hom.comp
        (rightTensorBaseChangeEquiv f P).toLinearMap := by
  apply hom_ext_unit f
  intro p
  simpa using (DFunLike.congr_fun (rightBaseChangeUnit_naturality f a) p).symm

/-- The actual balanced quotient is finitely generated. -/
instance tensor_finite : Module.Finite Sᵐᵒᵖ (Tensor f P.obj) :=
  Module.Finite.equiv (rightTensorBaseChangeEquiv f P).symm

/-- The actual balanced quotient is projective, without target flatness. -/
instance tensor_projective : Module.Projective Sᵐᵒᵖ (Tensor f P.obj) :=
  Module.Projective.of_equiv (rightTensorBaseChangeEquiv f P).symm

/-- Scalar extension on finite projectives using the literal quotient, without shrinking. -/
def rightTensorBaseChange : Category.{u, u} Rᵐᵒᵖ ⥤ Category.{v, max u v} Sᵐᵒᵖ where
  obj P := ⟨ModuleCat.of Sᵐᵒᵖ (Tensor f P.obj), inferInstance, inferInstance⟩
  map a := (property Sᵐᵒᵖ).homMk (ModuleCat.ofHom (RightScalarExtension.map f a.hom.hom))
  map_id P := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    exact RightScalarExtension.map_id f
  map_comp a b := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    exact RightScalarExtension.map_comp f a.hom.hom b.hom.hom

instance rightTensorBaseChange_additive : (rightTensorBaseChange f).Additive where
  map_add := by
    intros P Q a b
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    exact RightScalarExtension.map_add f a.hom.hom b.hom.hom

/-- With independent ring universes, compare in the explicit common ambient module category. -/
@[colib_tag "COL-1294", colib_ref "quillen"
  "Quillen/Aglib/Algebra/Category/ModuleCat/FiniteProjectiveBaseChangeTensor.lean:130-143"
  "adaptation"
  "The lifted natural comparison with the chosen finite-projective scalar extension."]
def rightTensorBaseChangeLiftedIso :
    rightTensorBaseChange f ⋙ (property Sᵐᵒᵖ).ι ≅
      rightBaseChange f ⋙ (property Sᵐᵒᵖ).ι ⋙ ModuleCat.uliftFunctor.{u} Sᵐᵒᵖ :=
  NatIso.ofComponents (fun P =>
    ((rightTensorBaseChangeEquiv f P).trans ULift.moduleEquiv.symm).toModuleIso) (by
      intro P Q a
      apply ModuleCat.hom_ext
      apply hom_ext_unit f
      intro p
      apply ULift.ext
      change rightTensorBaseChangeEquiv f Q
          (RightScalarExtension.map f a.hom.hom (unit f p)) =
        ((rightBaseChange f).map a).hom.hom (rightTensorBaseChangeEquiv f P (unit f p))
      exact DFunLike.congr_fun (rightTensorBaseChangeEquiv_naturality f a) (unit f p))

/-- The lifted natural comparison retains the original unit, including its universe lift. -/
theorem rightTensorBaseChangeLiftedIso_unit (p : P.obj) :
    (rightTensorBaseChangeLiftedIso f).hom.app P (unit f p) =
      ULift.up (rightBaseChangeUnit f P p) := by
  apply ULift.ext
  exact rightTensorBaseChangeEquiv_unit f P p

section SameUniverse

variable {S' : Type u} [Ring S'] (f' : R →+* S')

/-- In a common ring universe the canonical comparison is a finite-projective natural iso. -/
def rightTensorBaseChangeIso : rightTensorBaseChange f' ≅ rightBaseChange f' :=
  NatIso.ofComponents (fun P =>
    (property S'ᵐᵒᵖ).isoMk (rightTensorBaseChangeEquiv f' P).toModuleIso) (by
      intro P Q a
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      exact rightTensorBaseChangeEquiv_naturality f' a)

end SameUniverse

end ModuleCat.FiniteProjective
