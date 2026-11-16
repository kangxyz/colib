/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinatePullbackIso
public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinatePullbackScalar
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictBifunctor

/-! # The actual negative twist map is the polynomial scalar on the negative chart -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory Opposite TensorProduct
open Stacks.RelativeVeryAmple (tensorModules)
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication
open Stacks.AlgebraicGeometry.PullbackSectionMul
open Stacks.PullbackTensorCoherence Stacks.RingedSpace
open Stacks.RegularSequence (globalSmulCenter)
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

attribute [local instance] schemeTensorStrict

set_option backward.isDefEq.respectTransparency false in
/-- A scalar in the second tensor factor is multiplication by that scalar on the product. -/
theorem whiskerLeft_globalSmulCenter (X : Scheme.{u}) (r : Γ(X, ⊤)) (A B : X.Modules) :
    A ◁ (globalSmulCenter X r).app B = (globalSmulCenter X r).app (A ⊗ B) := by
  have h := Stacks.SheafOfModules.Strict.whiskerLeft_eq_tensorSheafBifunctor_map
    (⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩) A ((globalSmulCenter X r).app B)
  refine h.trans ?_
  refine Stacks.SheafOfModules.OnSpace.tensor_hom_ext X.toRingedSpace fun U a b => ?_
  obtain ⟨U⟩ := U
  let : Module (X.toRingedSpace.presheaf.obj (op U))
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj B).val.obj (op U)) :=
    Stacks.SheafOfModules.Tensor.ringSheafSectionModule
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩ (op U) _
  have hmap := tensorSheafMap_app_toTensorSheafSection X.toRingedSpace A B A B (𝟙 A)
    ((globalSmulCenter X r).app B) U a b
  refine hmap.trans ?_
  change toTensorSheafSection X.toRingedSpace A B (op U)
      (a ⊗ₜ[X.presheaf.obj (op U)] (X.presheaf.map U.leTop.op r • b)) =
    X.presheaf.map U.leTop.op r •
      toTensorSheafSection X.toRingedSpace A B (op U) (a ⊗ₜ[X.presheaf.obj (op U)] b)
  rw [TensorProduct.tmul_smul]
  exact map_smul ((sheafifyUnit X.toRingedSpace
    (PresheafOfModules.tensorObj (O := X.presheaf) A.val B.val)).app (op U)).hom _ _

set_option backward.isDefEq.respectTransparency false in
/-- On the actual negative chart, the coordinate map for `T₀` is the one for `T₁` followed
by multiplication by the polynomial coordinate. -/
theorem negativeTwistCoordinate_pullback_zero (X : QuasiCompactSchemes.{u})
    (F : (projectiveSpaceOver 1 X.obj).Modules) :
    let U := negativeChart X.obj
    (Scheme.Modules.pullback U.ι).map (negativeTwistCoordinate X.obj 0 F) =
      (Scheme.Modules.pullback U.ι).map (negativeTwistCoordinate X.obj 1 F) ≫
        (globalSmulCenter U.toScheme (negativeChartCoordinate X)).app
          ((Scheme.Modules.pullback U.ι).obj F) := by
  let U := negativeChart X.obj
  let f := U.ι
  let g := f.toLRSHom.toShHom
  let : MonoidalCategory (SheafOfModules (structureRingSheaf U.toScheme.toRingedSpace)) :=
    Stacks.PullbackGradedAlgebra.monoidalCategory U.toScheme.toRingedSpace
  let : MonoidalCategory
      (SheafOfModules (structureRingSheaf (projectiveSpaceOver 1 X.obj).toRingedSpace)) :=
    Stacks.PullbackGradedAlgebra.monoidalCategory (projectiveSpaceOver 1 X.obj).toRingedSpace
  let M := tensorModules (projectiveSpaceOver 1 X.obj) F (twistOver 1 X.obj (-1))
  let L := twistOver 1 X.obj 1
  let c := globalSmulCenter U.toScheme (negativeChartCoordinate X)
  let μ (k : Fin 2) := twistNegOneMulSection 1 X.obj F (coordinateSection X.obj k)
  let τ (k : Fin 2) := sectionHom L (coordinateSection X.obj k)
  let H := pullbackFunctor g
  let Q := pullbackTensorComparison g M L
  let : IsIso Q := isIso_pullbackTensorComparison g M L
  have h (k : Fin 2) : H.map (μ k) ≫ Q =
      (ρ_ (H.obj M)).inv ≫ (H.obj M ◁ negativeChartCoordinateUnitHom X k) := by
    have hk := pullbackTensorComparison_mulSection g M L (τ k)
    change H.map ((ρ_ M).inv ≫ M ◁ τ k) ≫ Q = _ at hk
    have hm : μ k = (ρ_ M).inv ≫ M ◁ τ k :=
      twistNegOneMulSection_eq_whisker X.obj F (coordinateSection X.obj k)
    rw [← hm] at hk
    exact hk.trans (congrArg (fun t => (ρ_ (H.obj M)).inv ≫ (H.obj M ◁ t))
      (congrArg (· ≫ H.map (τ k))
        (Stacks.PullbackUnitComparisonSection.inv_pullbackUnitComparison g)))
  have hμ : H.map (μ 0) = H.map (μ 1) ≫
      c.app (H.obj (tensorModules (projectiveSpaceOver 1 X.obj) M L)) := by
    apply (cancel_mono (asIso Q).hom).mp
    change H.map (μ 0) ≫ Q = (H.map (μ 1) ≫ _) ≫ Q
    rw [h 0, negativeChartCoordinateUnitHom_zero, whiskerLeft_comp, Category.assoc,
      whiskerLeft_globalSmulCenter]
    rw [← Category.assoc, ← h 1, Category.assoc]
    exact congrArg (fun k => H.map (μ 1) ≫ k) (c.naturality Q)
  let J := (twistNegOneTensorIso 1 X.obj F).hom
  have hn (k : Fin 2) : negativeTwistCoordinate X.obj k F = μ k ≫ J :=
    twistSectionMulNegOne_eq_comp 1 X.obj F (coordinateSection X.obj k)
  change H.map (negativeTwistCoordinate X.obj 0 F) =
    H.map (negativeTwistCoordinate X.obj 1 F) ≫ c.app (H.obj F)
  rw [hn 0, hn 1, Functor.map_comp, Functor.map_comp, hμ, Category.assoc,
    ← c.naturality (H.map J), Category.assoc]

end AlgebraicGeometry.Scheme.ProjectiveLine
