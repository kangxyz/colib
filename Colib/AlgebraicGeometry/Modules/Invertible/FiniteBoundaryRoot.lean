/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.Modules.Invertible.FiniteBoundaryFrame
public import StacksFrontier.AlgebraicGeometry.PicardGroup.TensorPower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPullback

/-!
# Tensor roots with a compatible finite-boundary frame

The boundary tensor-power trivialization is the composite of the native pullback/tensor-power
comparison, the pullback of the specified global root isomorphism, and the specified boundary
trivialization. The resulting frame equation holds on the entire finite boundary.
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.SheafOfModules.Invertible

universe u v

namespace AlgebraicGeometry

local instance (S : Scheme.{v}) :
    ∀ U, IsMulCommutative ((ringSheaf S).obj.obj U) :=
  fun U => inferInstanceAs (IsMulCommutative (S.presheaf.obj U))

local instance {D X : Scheme.{v}} (i : D ⟶ X) (M : X.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    Stacks.SheafOfModules.IsInvertible D.presheaf (ringSheafCond D)
      ((Scheme.Modules.pullback i).obj M) :=
  Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj i.toLRSHom.toShHom M

local instance {D X : Scheme.{v}} (i : D ⟶ X) (M : X.Modules)
    [hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M] :
    SheafOfModules.IsInvertible D.presheaf (ringSheafCond D)
      ((Scheme.Modules.pullback i).obj M) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ inferInstance

/-- The native pullback/tensor-power comparison, expressed using scheme modules. -/
def Scheme.Modules.pullbackIntegerTensorPowerIso {D X : Scheme.{v}} (i : D ⟶ X)
    (M : X.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M) (n : ℤ) :
    letI := hM
    (Scheme.Modules.pullback i).obj (Stacks.SheafOfModules.schemeTensorPower X M hM n) ≅
      tensorPower D.presheaf (ringSheafCond D) ((Scheme.Modules.pullback i).obj M) n := by
  letI := hM
  exact Stacks.TensorPowerPullback.pullbackIntPowIso i.toLRSHom.toShHom M n

/-- Every specified global root admits a frame compatible with the specified trivialization
of its target on a module-finite boundary, without any initial-frame or reducedness input. -/
@[colib_tag "COL-1212",
  colib_ref "axiom_stacks_5ed82d14"
    "Algebra/Category/ModuleCat/Sheaf/TensorPowerPullback.lean:180-186"
    "ingredient" "The native pullback comparison for integer tensor powers"]
theorem exists_root_compatible_frame_of_module_finite
    (R : Type u) [CommRing R] [StrictlyHenselianLocalRing R]
    (B : Type v) [CommRing B] [Algebra R B] [Module.Finite R B]
    {X : Scheme.{v}} (i : Spec (CommRingCat.of B) ⟶ X)
    (M L : X.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M)
    {n : ℕ} (hn : IsUnit (n : R))
    (α : Stacks.SheafOfModules.schemeTensorPower X M hM (n : ℤ) ≅ L)
    (τ : (Scheme.Modules.pullback i).obj L ≅
      SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B)))) :
    letI := hM
    ∃ e : (Scheme.Modules.pullback i).obj M ≅
        SheafOfModules.unit (ringSheaf (Spec (CommRingCat.of B))),
      tensorPowerMap (Spec (CommRingCat.of B)) e n ≪≫
        structureSheafTensorPowerIso (Spec (CommRingCat.of B)) n =
      (Scheme.Modules.pullbackIntegerTensorPowerIso i M hM (n : ℤ)).symm ≪≫
        (Scheme.Modules.pullback i).mapIso α ≪≫ τ := by
  let := hM
  exact exists_compatible_pullback_frame_of_module_finite R B i M hn
    ((Scheme.Modules.pullbackIntegerTensorPowerIso i M hM (n : ℤ)).symm ≪≫
      (Scheme.Modules.pullback i).mapIso α ≪≫ τ)

end AlgebraicGeometry
