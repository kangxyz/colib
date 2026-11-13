/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.ReducedFunctor
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedComparison.CancellationRepresentable

/-!
# Reduced derived torus cancellation on representables

The original cancellation map identifies the smooth motive with the
actual kernel of derived unit restriction. The isomorphism retains the
original exterior product on signed correspondences.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe w w' w'' u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [PerfectField k]

local notation "C" => singularSheafCochainFunctor k 0 ⋙ DerivedCategory.Q

private def cancellationRepresentableLimitCone (Y : Cor k) :
    LimitCone (parallelPair
      ((torusSectionsDerivedUnitRestriction k).app ((C).obj (torusCancellationCoefficients k Y)))
      0) :=
  ⟨KernelFork.ofι (cancellationRepresentableDerivedMap k Y)
    (cancellationRepresentableDerivedMap_unit k Y), cancellationRepresentableDerivedIsLimit k Y⟩

/-- The original cancellation map identifies a smooth representable with
the reduced derived torus sections of its unit-quotient motive. -/
@[no_expose]
def cancellationRepresentableReducedDerivedIso (Y : Cor k) :
    (C).obj ((representableLarge k).obj Y) ≅
      (reducedTorusSectionsDerivedFunctor k).obj ((C).obj (torusCancellationCoefficients k Y)) :=
  (limit.isoLimitCone (cancellationRepresentableLimitCone k Y)).symm

/-- After including the reduced summand, the isomorphism is the original
exterior-product comparison. -/
@[reassoc]
theorem cancellationRepresentableReducedDerivedIso_hom_inclusion (Y : Cor k) :
    (cancellationRepresentableReducedDerivedIso k Y).hom ≫
        (reducedTorusSectionsDerivedInclusion k).app ((C).obj (torusCancellationCoefficients k Y)) =
      cancellationRepresentableDerivedMap k Y := by
  unfold cancellationRepresentableReducedDerivedIso reducedTorusSectionsDerivedInclusion
  exact limit.isoLimitCone_inv_π (cancellationRepresentableLimitCone k Y) WalkingParallelPair.zero

/-- The isomorphism commutes with the original signed postcomposition
maps between smooth representing targets. -/
@[reassoc]
theorem cancellationRepresentableReducedDerivedIso_hom_naturality
    {Y Y' : Cor k} (β : Y ⟶ Y') :
    (C).map ((representableLarge k).map β) ≫
        (cancellationRepresentableReducedDerivedIso k Y').hom =
      (cancellationRepresentableReducedDerivedIso k Y).hom ≫
        (reducedTorusSectionsDerivedFunctor k).map
          ((C).map (torusCancellationCoefficientsMap k β)) := by
  let K := (C).obj (torusCancellationCoefficients k Y')
  let ι := reducedTorusSectionsDerivedInclusion k
  let : Mono (ι.app K) := inferInstanceAs
    (Mono (kernel.ι ((torusSectionsDerivedUnitRestriction k).app K)))
  apply (cancel_mono (ι.app K)).mp
  simp only [K, ι, Category.assoc, (reducedTorusSectionsDerivedInclusion k).naturality,
    cancellationRepresentableReducedDerivedIso_hom_inclusion]
  let f := (C).map (torusCancellationCoefficientsMap k β)
  exact (cancellationRepresentableDerivedMap_naturality k β).trans
    (cancellationRepresentableReducedDerivedIso_hom_inclusion_assoc k Y
      ((torusSectionsDerivedFunctor k).map f)).symm

end AlgebraicGeometry.SheafWithTransfers
