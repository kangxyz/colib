/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation

/-!
# Naturality of the torus cancellation comparison in the target

A signed correspondence in the representing target induces the original
postcomposition map on both torus products. Its quotient and unit-kernel
maps commute with the exterior comparison and its Suslin complex map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject Sₖ
local notation "Bₖ" => SmoothSite.base Sₖ

/-- The postcomposition map on the actual unit-section quotients. -/
def torusCancellationCoefficientsMap {Y Y' : Cor k} (β : Y ⟶ Y') :
    torusCancellationCoefficients k Y ⟶ torusCancellationCoefficients k Y' :=
  cokernel.map ((representableLarge k).map (torusUnitCorrespondence k Y))
    ((representableLarge k).map (torusUnitCorrespondence k Y'))
    ((representableLarge k).map ((Cor.parameterProduct Bₖ).map β))
    ((representableLarge k).map ((Cor.parameterProduct Gₘ).map β)) (by
      rw [← (representableLarge k).map_comp, ← (representableLarge k).map_comp]
      exact congrArg (representableLarge k).map
        ((Cor.parameterProductMap (SmoothSite.torusOne Sₖ)).naturality β).symm)

@[reassoc]
theorem toTorusCancellationCoefficients_map {Y Y' : Cor k} (β : Y ⟶ Y') :
    toTorusCancellationCoefficients k Y ≫ torusCancellationCoefficientsMap k β =
      (representableLarge k).map ((Cor.parameterProduct Gₘ).map β) ≫
        toTorusCancellationCoefficients k Y' :=
  cokernel.π_desc _ _ _

/-- Postcomposition on the target quotient and the source unit kernel. -/
def torusCancellationTargetMap {Y Y' : Cor k} (β : Y ⟶ Y') :
    torusCancellationTarget k Y ⟶ torusCancellationTarget k Y' :=
  kernel.map (torusUnit (torusCancellationCoefficients k Y))
    (torusUnit (torusCancellationCoefficients k Y'))
    (withParameterMap (torusCancellationCoefficientsMap k β) Gₘ)
    (withParameterMap (torusCancellationCoefficientsMap k β) Bₖ)
    (parameterPullback_coefficient_naturality (torusCancellationCoefficientsMap k β)
      (SmoothSite.torusOne Sₖ))

@[reassoc]
theorem torusCancellationTargetMap_ι {Y Y' : Cor k} (β : Y ⟶ Y') :
    torusCancellationTargetMap k β ≫ kernel.ι (torusUnit (torusCancellationCoefficients k Y')) =
      kernel.ι (torusUnit (torusCancellationCoefficients k Y)) ≫
        withParameterMap (torusCancellationCoefficientsMap k β) Gₘ :=
  kernel.lift_ι _ _ _

/-- Exterior product and the two unit reductions commute with signed
postcomposition in the representing target. -/
@[reassoc]
theorem torusCancellationMap_naturality {Y Y' : Cor k} (β : Y ⟶ Y') :
    (representableLarge k).map β ≫ torusCancellationMap k Y' =
      torusCancellationMap k Y ≫ torusCancellationTargetMap k β := by
  apply (cancel_mono (kernel.ι (torusUnit (torusCancellationCoefficients k Y')))).mp
  simp only [Category.assoc, torusCancellationMap_ι, torusCancellationTargetMap_ι]
  rw [← Category.assoc, torusCancellationMap_ι]
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  ext a
  obtain ⟨α⟩ := a
  let X := U.unop
  let F := Cor.parameterProduct Gₘ
  let R := representableLarge k
  let q := toTorusCancellationCoefficients k Y
  let q' := toTorusCancellationCoefficients k Y'
  let b := torusCancellationCoefficientsMap k β
  change (torusCancellationParameterMap k Y').hom.app (op X)
      ((R.map β).hom.app (op X) (ULift.up α)) =
    b.hom.app (op (F.obj X))
      ((torusCancellationParameterMap k Y).hom.app (op X) (ULift.up α))
  rw [representableLarge_map_app_apply, torusCancellationParameterMap_app_apply,
    torusCancellationParameterMap_app_apply, F.map_comp]
  have h := congrArg
    (fun f : R.obj (F.obj Y) ⟶ torusCancellationCoefficients k Y' ↦
      f.hom.app (op (F.obj X)) (ULift.up (F.map α)))
    (toTorusCancellationCoefficients_map k β)
  change b.hom.app (op (F.obj X))
      (q.hom.app (op (F.obj X)) (ULift.up (F.map α))) =
    q'.hom.app (op (F.obj X))
      ((R.map (F.map β)).hom.app (op (F.obj X)) (ULift.up (F.map α))) at h
  rw [representableLarge_map_app_apply] at h
  exact h.symm

/-- The same postcomposition equation on the native Suslin complexes. -/
@[reassoc, colib_tag "COL-1039"]
theorem torusCancellationChainMap_naturality {Y Y' : Cor k} (β : Y ⟶ Y') :
    singularComplexMap ((representableLarge k).map β) ≫ torusCancellationChainMap k Y' =
      torusCancellationChainMap k Y ≫ singularComplexMap (torusCancellationTargetMap k β) := by
  let F := singularComplexFunctor.{u + 1} (k := k)
  change F.map ((representableLarge k).map β) ≫ F.map (torusCancellationMap k Y') =
    F.map (torusCancellationMap k Y) ≫ F.map (torusCancellationTargetMap k β)
  rw [← F.map_comp, ← F.map_comp, torusCancellationMap_naturality]

end AlgebraicGeometry.PresheafWithTransfers
