/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.Sheafified
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.Naturality
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedComparison.SingularCoefficientNaturality
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedComparison.SingularReduced

/-!
# The reduced derived cancellation map on a smooth representable

The actual Suslin map takes the original smooth representable to the
source-unit kernel on its target-unit quotient. The derived torus
comparison identifies that summand with the kernel of evaluation at
the original unit on the total derived torus sections.
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
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

local notation "C" => singularSheafCochainFunctor k 0 ⋙ DerivedCategory.Q

/-- The original exterior product, followed by the target quotient and the
actual derived torus comparison. -/
def cancellationRepresentableDerivedMap (Y : Cor k) :
    (C).obj ((representableLarge k).obj Y) ⟶
      (torusSectionsDerivedFunctor k).obj ((C).obj (torusCancellationCoefficients k Y)) :=
  DerivedCategory.Q.map (torusCancellationSheafCochainMap k Y) ≫
    singularDerivedTorusKernelInclusion k (torusCancellationCoefficients k Y)

/-- The map retains the actual exterior product on the signed representable
and its original target-unit quotient. -/
theorem cancellationRepresentableDerivedMap_eq_parameterMap (Y : Cor k) :
    cancellationRepresentableDerivedMap k Y =
      (C).map (torusCancellationParameterMap k Y) ≫
        singularSheafDerivedTorusSectionsMap k (torusCancellationCoefficients k Y) := by
  let E := C
  let P := torusCancellationCoefficients k Y
  change E.map (torusCancellationMap k Y) ≫
      (E.map (kernel.ι (torusUnit P)) ≫ singularSheafDerivedTorusSectionsMap k P) =
    E.map (torusCancellationParameterMap k Y) ≫ singularSheafDerivedTorusSectionsMap k P
  rw [← Category.assoc, ← E.map_comp, torusCancellationMap_ι]

/-- The original reduced comparison is natural for each signed
correspondence of smooth representing targets. -/
theorem cancellationRepresentableDerivedMap_naturality {Y Y' : Cor k} (β : Y ⟶ Y') :
    (C).map ((representableLarge k).map β) ≫ cancellationRepresentableDerivedMap k Y' =
      cancellationRepresentableDerivedMap k Y ≫ (torusSectionsDerivedFunctor k).map
        ((C).map (torusCancellationCoefficientsMap k β)) := by
  let F := C
  let T := SmoothSite.multiplicativeGroupObject (Spec (.of k))
  let P := torusCancellationCoefficients k Y
  let Q := torusCancellationCoefficients k Y'
  let f := torusCancellationCoefficientsMap k β
  let a := torusCancellationParameterMap k Y
  let b := torusCancellationParameterMap k Y'
  have hn : (representableLarge k).map β ≫ b = a ≫ withParameterMap f T := by
    calc
      _ = (representableLarge k).map β ≫ torusCancellationMap k Y' ≫
          kernel.ι (torusUnit Q) :=
        congrArg ((representableLarge k).map β ≫ ·) (torusCancellationMap_ι k Y').symm
      _ = torusCancellationMap k Y ≫ (torusCancellationTargetMap k β ≫
          kernel.ι (torusUnit Q)) := by
        rw [torusCancellationMap_naturality_assoc]
      _ = _ := by
        rw [torusCancellationTargetMap_ι, ← Category.assoc, torusCancellationMap_ι]
  rw [cancellationRepresentableDerivedMap_eq_parameterMap,
    cancellationRepresentableDerivedMap_eq_parameterMap]
  calc
    _ = F.map ((representableLarge k).map β ≫ b) ≫
        singularSheafDerivedTorusSectionsMap k Q := by
      change F.map ((representableLarge k).map β) ≫
          (F.map b ≫ singularSheafDerivedTorusSectionsMap k Q) = _
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ singularSheafDerivedTorusSectionsMap k Q) (F.map_comp _ _).symm)
    _ = F.map (a ≫ withParameterMap f T) ≫ singularSheafDerivedTorusSectionsMap k Q :=
      congrArg (fun x => F.map x ≫ singularSheafDerivedTorusSectionsMap k Q) hn
    _ = _ := by
      change F.map (a ≫ withParameterMap f T) ≫ singularSheafDerivedTorusSectionsMap k Q =
        (F.map a ≫ singularSheafDerivedTorusSectionsMap k P) ≫ _
      rw [F.map_comp, Category.assoc]
      exact (congrArg (F.map a ≫ ·) (singularSheafDerivedTorusSectionsMap_naturality k f)).trans
        (Category.assoc _ _ _).symm

/-- The original cancellation map lands in the reduced derived summand. -/
@[reassoc]
theorem cancellationRepresentableDerivedMap_unit (Y : Cor k) :
    cancellationRepresentableDerivedMap k Y ≫
      (torusSectionsDerivedUnitRestriction k).app ((C).obj (torusCancellationCoefficients k Y)) =
        0 := by
  rw [cancellationRepresentableDerivedMap, Category.assoc,
    singularDerivedTorusKernelInclusion_unit, comp_zero]

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [PerfectField k]

/-- For the original smooth representable, cancellation exhibits its
singular motive as the actual reduced right-derived torus summand of
the singular motive of the target quotient. -/
def cancellationRepresentableDerivedIsLimit (Y : Cor k) :
    IsLimit (KernelFork.ofι (cancellationRepresentableDerivedMap k Y)
      (cancellationRepresentableDerivedMap_unit k Y)) := by
  let P := torusCancellationCoefficients k Y
  let q := torusCancellationSheafCochainMap k Y
  let : QuasiIso q := torusCancellationSheafCochainMap_quasiIso k Y
  let e := asIso (DerivedCategory.Q.map q)
  let r := (torusSectionsDerivedUnitRestriction k).app ((C).obj P)
  exact IsKernel.isoKernel r (cancellationRepresentableDerivedMap k Y)
    (singularDerivedTorusKernelIsLimit k P) e rfl

end AlgebraicGeometry.SheafWithTransfers
