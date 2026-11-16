/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.FlasquePushforwardComparison
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsShortExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry

/-! # The projection formula for the twisted diagonal coefficient

An invertible twist pulled back from the first factor can be moved through
the ordinary first projection. It also preserves acyclicity for that
projection. The latter does not require the twisted sheaf to be flasque.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.ProjectionFormula

namespace AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance 2000] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false

variable {Y Z : Scheme.{u}} (f : Z ⟶ Y) (L : Y.Modules)

/-- Left tensor by a module, at the native scheme-module spelling. -/
abbrev diagonalTwistTensor {S : Scheme.{u}} (M : S.Modules) : S.Modules ⥤ S.Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.sheaf).obj M

local notation "L'" => Functor.obj (pullback f) L

variable [Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]

local instance (S : Scheme.{u}) (M : S.Modules) :
    (diagonalTwistTensor M).PreservesZeroMorphisms :=
  Stacks.Sheaves.ChangeOfRings.preservesZeroMorphisms_sheafTensorObj S.sheaf M

/-- The sheaf tensor braiding, in left and right functor notation. -/
def twistProjectionBraiding (S : Scheme.{u}) (M : S.Modules) :
    diagonalTwistTensor M ≅ tensorRightInvertible S M :=
  ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding S.sheaf).app M) ≪≫
    (CategoryTheory.Functor.tensorRightOfUncurryIso
      (Stacks.SheafOfModules.Tensor.sheafTensor S.sheaf) M).symm

/-- The ordinary projection formula for tensoring with a pulled-back invertible sheaf
on the left, naturally in the coefficient. -/
def pushforwardTensorLeftInvertibleNatIso :
    diagonalTwistTensor L' ⋙ pushforward f ≅ pushforward f ⋙ diagonalTwistTensor L :=
  Functor.isoWhiskerRight (twistProjectionBraiding Z L') _ ≪≫
    pushforwardTensorRightNatIso f L ≪≫
    Functor.isoWhiskerLeft _ (twistProjectionBraiding Y L).symm

/-- Higher direct-image vanishing is preserved by the pulled-back invertible twist.
The ordinary, natural-number indexed right derived functors are independent of the chosen
derived-category instance. -/
theorem isZero_rightDerived_tensorLeftPullbackInvertible (M : Z.Modules)
    (n : ℕ) (hM : IsZero (((pushforward f).rightDerived n).obj M)) :
    IsZero (((pushforward f).rightDerived n).obj ((diagonalTwistTensor L').obj M)) := by
  let := AlgebraicGeometry.Scheme.Modules.hasDerivedCategory Z
  let := AlgebraicGeometry.Scheme.Modules.hasDerivedCategory Y
  let F := pushforward f
  have hZ := (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff F n M).1 hM
  apply (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff F n _).2
  let e := (twistProjectionBraiding Z L').app M
  let hzero := (tensorRightInvertible Y L).map_isZero hZ
  exact hzero.of_iso ((F.rightDerivedPlus (n : ℤ)).mapIso e ≪≫
    (higherDirectImageTensorRightIso f L (n : ℤ)).app M)

/-- Tensoring a sheaf by the pullback of an invertible sheaf preserves right acyclicity
for the direct image. -/
theorem rightAcyclic_tensorLeftPullbackInvertible (M : Z.Modules)
    (hM : (pushforward f).rightAcyclic M) :
    (pushforward f).rightAcyclic ((diagonalTwistTensor L').obj M) := by
  apply (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat (pushforward f) _).2
  intro n hn
  exact isZero_rightDerived_tensorLeftPullbackInvertible f L M n
    ((Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat (pushforward f) M).1 hM n hn)

/-- The ordinary projection formula on the actual degreewise complexes. -/
def pushforwardTensorLeftInvertibleCochainIso :
    ((diagonalTwistTensor L').mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
      (pushforward f).mapHomologicalComplex (ComplexShape.up ℤ) ≅
    (pushforward f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      (diagonalTwistTensor L).mapHomologicalComplex (ComplexShape.up ℤ) :=
  let A := diagonalTwistTensor L'
  let B := diagonalTwistTensor L
  let F := pushforward f
  let : (A ⋙ F).PreservesZeroMorphisms := Functor.preservesZeroMorphisms_comp A F
  let : (F ⋙ B).PreservesZeroMorphisms := Functor.preservesZeroMorphisms_comp F B
  NatIso.mapHomologicalComplex (pushforwardTensorLeftInvertibleNatIso f L)
    (ComplexShape.up ℤ)

/-- The pushforward of a resolution of an invertibly twisted, termwise acyclic complex
is a quasi-isomorphism. This keeps the actual chain map of the resolution. -/
theorem quasiIso_pushforward_tensorLeftPullbackInvertible_resolution
    {H J : CochainComplex Z.Modules ℤ}
    (b : ((diagonalTwistTensor L').mapHomologicalComplex (ComplexShape.up ℤ)).obj H ⟶ J)
    [QuasiIso b]
    (hH : CochainComplex.plus Z.Modules
      (((diagonalTwistTensor L').mapHomologicalComplex (ComplexShape.up ℤ)).obj H))
    (hJ : CochainComplex.plus Z.Modules J)
    (hac : ∀ n, (pushforward f).rightAcyclic (H.X n))
    (hfl : ∀ n, TopCat.Sheaf.IsFlasque
      ((_root_.SheafOfModules.toSheaf Z.ringCatSheaf).obj (J.X n))) :
    QuasiIso (((pushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).map b) :=
  (pushforward f).quasiIso_mapHomologicalComplex_of_rightAcyclic b hH hJ
    (fun n => rightAcyclic_tensorLeftPullbackInvertible f L (H.X n) (hac n))
    (fun n => pushforward_rightAcyclic_of_flasque f _ (hfl n))

end AlgebraicGeometry.Scheme.Modules
