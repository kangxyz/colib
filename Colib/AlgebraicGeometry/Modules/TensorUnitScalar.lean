/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectGlobalScalar
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidalPreadditive

/-! # The tensor unit and global scalar multiplication

The sheaf tensor and unitor are Stacks' existing tensor on modules over a ringed space.
The scalar identity is proved on local pure tensors, as in Quillen's
`PerfectComplexes/TensorToUnit.lean` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
No perfect-complex model or substitute identity tensor functor is introduced.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Stacks.RegularSequence (globalSmulCenter globalSmulCenter_app_app)
open Stacks.SheafOfModules.OnSpace

universe u
namespace AlgebraicGeometry.Scheme.Modules

local instance tensorUnitScalarMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := monoidal X.toRingedSpace
local instance tensorUnitScalarPreadditive (X : Scheme.{u}) :
    MonoidalPreadditive X.Modules :=
  monoidalPreadditive X.toRingedSpace

/-- The native sheaf coefficient scalar, followed by the native tensor left unitor,
is the same global scalar on the second factor. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/TensorToUnit.lean:30-50"
  "adaptation" "The actual tensor-unit scalar identity on local pure tensors"]
theorem tensorUnit_globalScalar_unitor (X : Scheme.{u}) (r : Γ(X, ⊤)) (M : X.Modules) :
    ((globalSmulCenter X r).app (𝟙_ X.Modules) ▷ M) ≫ (λ_ M).hom =
      (λ_ M).hom ≫ (globalSmulCenter X r).app M := by
  apply tensor_hom_ext X.toRingedSpace
  intro U a m
  change (((λ_ M).hom).val.app U).hom
      ((((globalSmulCenter X r).app (𝟙_ X.Modules) ▷ M).val.app U).hom
        (tensorObjTmul X.toRingedSpace _ M U a m)) = _
  rw [whiskerRight_tmul]
  let a' : X.presheaf.obj U := a
  let s : X.presheaf.obj U := X.presheaf.map U.unop.leTop.op r
  change (((λ_ M).hom).val.app U).hom
      (tensorObjTmul X.toRingedSpace _ M U
        (unitSection X.toRingedSpace U (s * a')) m) =
    s • (((λ_ M).hom).val.app U).hom
      (tensorObjTmul X.toRingedSpace _ M U (unitSection X.toRingedSpace U a') m)
  exact (leftUnitor_tmul X.toRingedSpace M U (s * a') m).trans
    ((mul_smul s a' m).trans
      (congrArg (fun z => s • z) (leftUnitor_tmul X.toRingedSpace M U a' m).symm))

end AlgebraicGeometry.Scheme.Modules
