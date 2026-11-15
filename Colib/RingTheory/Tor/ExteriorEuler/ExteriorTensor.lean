/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.LinearAlgebra.TensorProduct.PushoutAction

/-!
# Exterior tensor products of modules over a field

The exterior tensor of modules over `A` and `B` is a module over `A ⊗[k] B` through
the pinned pushout action. The bifunctor is exact in each variable when `k` is a field.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory TensorProduct
open scoped ModuleCat.Algebra

namespace ModuleCat

universe u

variable {k A B : Type u} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]

attribute [local instance 10] Stacks.TensorProductPushout.pushoutModule

/-- The exterior tensor product with the factorwise `A ⊗[k] B` action. -/
abbrev exteriorTensorObj (k : Type u) [CommRing k] [Algebra k A] [Algebra k B]
    (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) : ModuleCat.{u} (A ⊗[k] B) :=
  ModuleCat.of (A ⊗[k] B) (M ⊗[k] N)

variable {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}

/-- The exterior tensor product of two linear maps over their respective rings. -/
def exteriorTensorMap (f : M ⟶ M') (g : N ⟶ N') :
    exteriorTensorObj k M N ⟶ exteriorTensorObj k M' N' :=
  let l := TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k)
  ModuleCat.ofHom
    { toFun := l
      map_add' := l.map_add
      map_smul' := by
        intro c x
        rw [RingHom.id_apply]
        induction c with
        | add c d hc hd => simp only [add_smul, l.map_add, hc, hd]
        | tmul a b =>
          induction x with
          | add x y hx hy => simp only [smul_add, l.map_add, hx, hy]
          | tmul m n =>
            change l ((a ⊗ₜ[k] b) • (m ⊗ₜ[k] n)) = (a ⊗ₜ[k] b) • l (m ⊗ₜ[k] n)
            simp only [Stacks.TensorProductPushout.pushoutModule_smul_tmul_tmul, l,
              TensorProduct.map_tmul, LinearMap.restrictScalars_apply, LinearMap.map_smul] }

/-- On pure tensors the exterior map applies the two maps factor by factor. -/
@[simp]
theorem exteriorTensorMap_tmul (f : M ⟶ M') (g : N ⟶ N') (m : M) (n : N) :
    exteriorTensorMap (k := k) f g (m ⊗ₜ[k] n) = f m ⊗ₜ[k] g n := rfl

/-- Maps from an exterior tensor product agree if they agree on its pure tensors. -/
theorem exteriorTensor_hom_ext {Z : ModuleCat.{u} (A ⊗[k] B)}
    {f g : exteriorTensorObj k M N ⟶ Z}
    (h : ∀ (m : M) (n : N), f (m ⊗ₜ[k] n) = g (m ⊗ₜ[k] n)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul m n => exact h m n
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Exterior tensor product, functorial in both modules. -/
def exteriorTensor : ModuleCat.{u} A ⥤ ModuleCat.{u} B ⥤ ModuleCat.{u} (A ⊗[k] B) :=
  Functor.curryObj
    { obj := fun X => exteriorTensorObj k X.1 X.2
      map := fun f => exteriorTensorMap f.1 f.2
      map_id := fun _ => exteriorTensor_hom_ext fun _ _ => rfl
      map_comp := fun _ _ => exteriorTensor_hom_ext fun _ _ => rfl }

/-- The map on an exterior tensor induced by a map of its first factor. -/
@[simp]
theorem exteriorTensor_map_app (f : M ⟶ M') (N : ModuleCat.{u} B) :
    ((exteriorTensor (k := k)).map f).app N = exteriorTensorMap (k := k) f (𝟙 N) := rfl

/-- The map on an exterior tensor induced by a map of its second factor. -/
@[simp]
theorem exteriorTensor_obj_map (M : ModuleCat.{u} A) (g : N ⟶ N') :
    ((exteriorTensor (k := k)).obj M).map g = exteriorTensorMap (k := k) (𝟙 M) g := rfl

@[simp]
theorem exteriorTensorMap_id (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) :
    exteriorTensorMap (k := k) (𝟙 M) (𝟙 N) = 𝟙 (exteriorTensorObj k M N) :=
  exteriorTensor_hom_ext fun _ _ => rfl

instance exteriorTensor_obj_additive (M : ModuleCat.{u} A) :
    ((exteriorTensor (k := k) (B := B)).obj M).Additive where
  map_add := by
    intros
    apply exteriorTensor_hom_ext
    intro m n
    exact TensorProduct.tmul_add _ _ _

instance exteriorTensor_additive : (exteriorTensor (k := k) (A := A) (B := B)).Additive where
  map_add := by
    intro X Y f g
    apply NatTrans.ext
    funext N
    apply exteriorTensor_hom_ext
    intro m n
    exact TensorProduct.add_tmul _ _ _

instance exteriorTensor_flip_obj_additive (N : ModuleCat.{u} B) :
    ((exteriorTensor (k := k) (A := A)).flip.obj N).Additive where
  map_add := by
    intros
    apply exteriorTensor_hom_ext
    intro m n
    exact TensorProduct.add_tmul _ _ _

end ModuleCat

namespace ModuleCat

universe u

variable {k A B : Type u} [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

private theorem exteriorTensor_obj_map_exact (M : ModuleCat.{u} A)
    (S : ShortComplex (ModuleCat.{u} B)) (h : S.Exact) :
    (S.map ((exteriorTensor (k := k)).obj M)).Exact := by
  apply ModuleCat.shortComplex_exact
  exact Module.Flat.lTensor_exact (R := k) M (f := S.f.hom.restrictScalars k)
    (g := S.g.hom.restrictScalars k)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp h)

private theorem exteriorTensor_flip_obj_map_exact (N : ModuleCat.{u} B)
    (S : ShortComplex (ModuleCat.{u} A)) (h : S.Exact) :
    (S.map ((exteriorTensor (k := k)).flip.obj N)).Exact := by
  apply ModuleCat.shortComplex_exact
  exact Module.Flat.rTensor_exact (R := k) N (f := S.f.hom.restrictScalars k)
    (g := S.g.hom.restrictScalars k)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp h)

instance exteriorTensor_obj_preservesHomology (M : ModuleCat.{u} A) :
    ((exteriorTensor (k := k) (B := B)).obj M).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (exteriorTensor_obj_map_exact M)

instance exteriorTensor_flip_obj_preservesHomology (N : ModuleCat.{u} B) :
    ((exteriorTensor (k := k) (A := A)).flip.obj N).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (exteriorTensor_flip_obj_map_exact N)

end ModuleCat
