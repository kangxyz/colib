/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.RingTheory.Tor.ExteriorEuler.ExteriorTensor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.RingTheory.Flat.Stability
public import StacksFrontier.Homology.ExtendScalars.Flat

/-!
# Scalar extension of exterior tensor products

Both inputs can be extended to the tensor product ring and tensored there. The
pinned cancellation isomorphism identifies that ordinary tensor with the exterior
tensor. This identifies the tensor of two exterior products with the exterior product
of the two ordinary tensors.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.MonoidalCategory TensorProduct
open scoped ModuleCat.Algebra ChangeOfRings

namespace ModuleCat

universe u

variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]

local notation "T" => A ⊗[k] B
local notation "ιA" => AlgHom.toRingHom (Algebra.TensorProduct.includeLeft : A →ₐ[k] T)
local notation "ιB" => AlgHom.toRingHom (Algebra.TensorProduct.includeRight : B →ₐ[k] T)

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance 10] Stacks.TensorProductPushout.pushoutModule

/-- The actions of the source ring on the scalar-extension tensor factors agree on elements.
The comparison keeps the `T`-module structure throughout. -/
def extendScalarsTensorIso {R : Type u} [CommRing R] [Algebra R T]
    (M : ModuleCat.{u} R) :
    (extendScalars (algebraMap R T)).obj M ≅ ModuleCat.of T (T ⊗[R] M) := by
  let V := (restrictScalars (algebraMap R T)).obj (ModuleCat.of T T)
  let e : V ≃ₗ[T] T := LinearEquiv.refl T T
  let eR : V ≃ₗ[R] T :=
    { e.toAddEquiv with
      map_smul' := fun r t => (Algebra.smul_def r (show T from t)).symm }
  letI : IsScalarTower R T V := ⟨fun r t v => by
    change ((r • t : T) * (show T from v)) = algebraMap R T r * (t * (show T from v))
    rw [Algebra.smul_def, mul_assoc]⟩
  let ℓ := TensorProduct.congr eR (LinearEquiv.refl R M)
  let e' : V ⊗[R] M ≃ₗ[T] T ⊗[R] M :=
    { ℓ with
      map_smul' := by
        intro r x
        rw [RingHom.id_apply]
        change ℓ (r • x) = r • ℓ x
        induction x using TensorProduct.inductionOn with
        | tmul x m => rfl
        | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
  exact e'.toModuleIso

/-- The exterior tensor is the ordinary tensor of the two scalar extensions. -/
def exteriorTensorExtendScalarsIso (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) :
    (extendScalars ιA).obj M ⊗ (extendScalars ιB).obj N ≅ exteriorTensorObj k M N := by
  let eA : (extendScalars ιA).obj M ≅ ModuleCat.of T (T ⊗[A] M) :=
    extendScalarsTensorIso (k := k) M
  let eB : (extendScalars ιB).obj N ≅ ModuleCat.of T (T ⊗[B] N) :=
    extendScalarsTensorIso (k := k) N
  exact (eA ⊗ᵢ eB) ≪≫ (Stacks.TensorProductPushout.cancelBaseChangePushout k A B M N).toModuleIso

/-- The comparison evaluated on pure tensors of scalar extensions. -/
theorem exteriorTensorExtendScalarsIso_hom_tmul_tmul
    (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) (a a' : A) (b b' : B) (m : M) (n : N) :
    (exteriorTensorExtendScalarsIso (k := k) M N).hom
      ((((a ⊗ₜ[k] b) ⊗ₜ[A,ιA] m) : (extendScalars ιA).obj M) ⊗ₜ[T]
        (((a' ⊗ₜ[k] b') ⊗ₜ[B,ιB] n) : (extendScalars ιB).obj N)) =
      ((a * a') • m) ⊗ₜ[k] ((b * b') • n) := by
  change Stacks.TensorProductPushout.cancelBaseChangePushout k A B M N
    (((a ⊗ₜ[k] b) ⊗ₜ[A] m) ⊗ₜ[T] ((a' ⊗ₜ[k] b') ⊗ₜ[B] n)) = _
  exact Stacks.TensorProductPushout.cancelBaseChangePushout_tmul_tmul k A B a a' b b' m n

/-- The inverse sends a pure tensor to the tensor of the two unit pure tensors. -/
theorem exteriorTensorExtendScalarsIso_inv_tmul
    (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) (m : M) (n : N) :
    (exteriorTensorExtendScalarsIso (k := k) M N).inv (m ⊗ₜ[k] n) =
      ((((1 : T) ⊗ₜ[A,ιA] m) : (extendScalars ιA).obj M) ⊗ₜ[T]
        (((1 : T) ⊗ₜ[B,ιB] n) : (extendScalars ιB).obj N)) := by
  change ((extendScalarsTensorIso (k := k) M).inv ⊗ₘ
      (extendScalarsTensorIso (k := k) N).inv)
    ((Stacks.TensorProductPushout.cancelBaseChangePushout k A B M N).symm (m ⊗ₜ[k] n)) = _
  rw [Stacks.TensorProductPushout.cancelBaseChangePushout_symm_tmul]
  rfl

variable {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}

/-- Naturality of the inverse comparison in the two input modules. -/
@[reassoc]
theorem exteriorTensorExtendScalarsIso_inv_naturality (f : M ⟶ M') (g : N ⟶ N') :
    exteriorTensorMap (k := k) f g ≫ (exteriorTensorExtendScalarsIso (k := k) M' N').inv =
      (exteriorTensorExtendScalarsIso (k := k) M N).inv ≫
        ((extendScalars ιA).map f ⊗ₘ (extendScalars ιB).map g) := by
  apply exteriorTensor_hom_ext (k := k) (M := M) (N := N)
    (Z := (extendScalars ιA).obj M' ⊗ (extendScalars ιB).obj N')
  intro m n
  change (exteriorTensorExtendScalarsIso (k := k) M' N').inv
      (exteriorTensorMap (k := k) f g (m ⊗ₜ[k] n)) =
    ((extendScalars ιA).map f ⊗ₘ (extendScalars ιB).map g)
      ((exteriorTensorExtendScalarsIso (k := k) M N).inv (m ⊗ₜ[k] n))
  rw [exteriorTensorMap_tmul, exteriorTensorExtendScalarsIso_inv_tmul,
    exteriorTensorExtendScalarsIso_inv_tmul, ModuleCat.MonoidalCategory.tensorHom_tmul,
    ModuleCat.ExtendScalars.map_tmul,
    ModuleCat.ExtendScalars.map_tmul]

/-- The exterior tensor of two flat modules is flat over the tensor product ring. -/
theorem flat_exteriorTensorObj (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)
    [Module.Flat A M] [Module.Flat B N] : Module.Flat T (exteriorTensorObj k M N) := by
  have : Module.Flat T ((T ⊗[A] M) ⊗[T] (T ⊗[B] N)) := inferInstance
  exact Module.Flat.of_linearEquiv
    (Stacks.TensorProductPushout.cancelBaseChangePushout k A B M N).symm

/-- Tensoring two exterior products is the exterior product of the two tensors. -/
def exteriorTensorTensorIso (M M' : ModuleCat.{u} A) (N N' : ModuleCat.{u} B) :
    exteriorTensorObj k M N ⊗ exteriorTensorObj k M' N' ≅
      exteriorTensorObj k (M ⊗ M') (N ⊗ N') :=
  ((exteriorTensorExtendScalarsIso (k := k) M N).symm ⊗ᵢ
      (exteriorTensorExtendScalarsIso (k := k) M' N').symm) ≪≫
    (TensorProduct.tensorTensorTensorComm T _ _ _ _).toModuleIso ≪≫
    (Functor.Monoidal.μIso (extendScalars ιA) M M' ⊗ᵢ
      Functor.Monoidal.μIso (extendScalars ιB) N N') ≪≫
    exteriorTensorExtendScalarsIso (k := k) (M ⊗ M') (N ⊗ N')

/-- On pure tensors the comparison groups the two `A` factors and the two `B` factors. -/
@[simp]
theorem exteriorTensorTensorIso_hom_tmul_tmul
    (M M' : ModuleCat.{u} A) (N N' : ModuleCat.{u} B)
    (m : M) (m' : M') (n : N) (n' : N') :
    (exteriorTensorTensorIso (k := k) M M' N N').hom
      (((m ⊗ₜ[k] n) : exteriorTensorObj k M N) ⊗ₜ[T]
        ((m' ⊗ₜ[k] n') : exteriorTensorObj k M' N')) =
      (m ⊗ₜ[A] m') ⊗ₜ[k] (n ⊗ₜ[B] n') := by
  have hμ (R : Type u) [CommRing R] (f : R →+* T) (X Y : ModuleCat.{u} R) (x : X) (y : Y) :
      (Functor.Monoidal.μIso (extendScalars f) X Y).hom
        ((((1 : T) ⊗ₜ[R,f] x) : (extendScalars f).obj X) ⊗ₜ[T]
          (((1 : T) ⊗ₜ[R,f] y) : (extendScalars f).obj Y)) =
        (1 : T) ⊗ₜ[R,f] (x ⊗ₜ[R] y) := by
    let := f.toAlgebra
    have h := ConcreteCategory.congr_hom
      ((Functor.Monoidal.μIso (extendScalars f) X Y).inv_hom_id)
      ((1 : T) ⊗ₜ[R,f] (x ⊗ₜ[R] y))
    change (Functor.Monoidal.μIso (extendScalars f) X Y).hom
        (Functor.OplaxMonoidal.δ (extendScalars f) X Y ((1 : T) ⊗ₜ[R,f] (x ⊗ₜ[R] y))) =
      (1 : T) ⊗ₜ[R,f] (x ⊗ₜ[R] y) at h
    rw [ModuleCat.extendScalars_δ_tmul] at h
    exact h
  have hunit (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B) (x : X) (y : Y) :
      (exteriorTensorExtendScalarsIso (k := k) X Y).hom
        ((((1 : T) ⊗ₜ[A,ιA] x) : (extendScalars ιA).obj X) ⊗ₜ[T]
          (((1 : T) ⊗ₜ[B,ιB] y) : (extendScalars ιB).obj Y)) = x ⊗ₜ[k] y := by
    rw [← exteriorTensorExtendScalarsIso_inv_tmul]
    exact ConcreteCategory.congr_hom (exteriorTensorExtendScalarsIso (k := k) X Y).inv_hom_id _
  change (exteriorTensorExtendScalarsIso (k := k) (M ⊗ M') (N ⊗ N')).hom
    (((Functor.Monoidal.μIso (extendScalars ιA) M M').hom ⊗ₘ
        (Functor.Monoidal.μIso (extendScalars ιB) N N').hom)
      (TensorProduct.tensorTensorTensorComm T _ _ _ _
        (((exteriorTensorExtendScalarsIso (k := k) M N).inv (m ⊗ₜ[k] n)) ⊗ₜ[T]
          ((exteriorTensorExtendScalarsIso (k := k) M' N').inv (m' ⊗ₜ[k] n'))))) = _
  rw [exteriorTensorExtendScalarsIso_inv_tmul, exteriorTensorExtendScalarsIso_inv_tmul,
    TensorProduct.tensorTensorTensorComm_tmul, ModuleCat.MonoidalCategory.tensorHom_tmul,
    hμ, hμ, hunit]

/-- Naturality of the comparison that groups the two ordinary tensors. -/
@[reassoc]
theorem exteriorTensorTensorIso_hom_naturality
    {P P' : ModuleCat.{u} A} {Q Q' : ModuleCat.{u} B}
    (f : M ⟶ M') (g : N ⟶ N') (f' : P ⟶ P') (g' : Q ⟶ Q') :
    (exteriorTensorMap (k := k) f g ⊗ₘ exteriorTensorMap (k := k) f' g') ≫
        (exteriorTensorTensorIso (k := k) M' P' N' Q').hom =
      (exteriorTensorTensorIso (k := k) M P N Q).hom ≫
        exteriorTensorMap (k := k) (f ⊗ₘ f') (g ⊗ₘ g') := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  change ((exteriorTensorMap (k := k) f g ⊗ₘ exteriorTensorMap (k := k) f' g') ≫
      (exteriorTensorTensorIso (k := k) M' P' N' Q').hom) (x ⊗ₜ[T] y) =
    ((exteriorTensorTensorIso (k := k) M P N Q).hom ≫
      exteriorTensorMap (k := k) (f ⊗ₘ f') (g ⊗ₘ g')) (x ⊗ₜ[T] y)
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [TensorProduct.add_tmul, map_add, map_add, hx, hx']
  | tmul m n =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => rw [TensorProduct.tmul_add, map_add, map_add, hy, hy']
    | tmul p q =>
      change (exteriorTensorTensorIso (k := k) M' P' N' Q').hom
          ((exteriorTensorMap (k := k) f g ⊗ₘ exteriorTensorMap (k := k) f' g')
            ((m ⊗ₜ[k] n) ⊗ₜ[T] (p ⊗ₜ[k] q))) =
        exteriorTensorMap (k := k) (f ⊗ₘ f') (g ⊗ₘ g')
          ((exteriorTensorTensorIso (k := k) M P N Q).hom
            ((m ⊗ₜ[k] n) ⊗ₜ[T] (p ⊗ₜ[k] q)))
      rw [ModuleCat.MonoidalCategory.tensorHom_tmul, exteriorTensorMap_tmul,
        exteriorTensorMap_tmul, exteriorTensorTensorIso_hom_tmul_tmul,
        exteriorTensorTensorIso_hom_tmul_tmul, exteriorTensorMap_tmul,
        ModuleCat.MonoidalCategory.tensorHom_tmul, ModuleCat.MonoidalCategory.tensorHom_tmul]

end ModuleCat
