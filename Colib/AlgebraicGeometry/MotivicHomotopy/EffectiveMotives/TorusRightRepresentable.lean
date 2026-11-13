/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Representable
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TorusRight
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedComparison.CancellationRepresentableReduced

/-!
# Reduced torus cancellation on effective representables

The native inclusion of effective motives lifts the original
representable cancellation isomorphism. The included map is the
original exterior-product map followed by derived torus comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers PresheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Qₑ" => singularEffectiveMotiveFunctor k
local notation "Rₑ" => effectiveReducedTorusSectionsFunctor k
local notation "Vₑ" => effectiveMotivesMinusToDerived k

/-- Cancellation identifies the effective smooth motive with the
reduced derived sections of the original target-unit quotient. -/
@[no_expose]
def effectiveMotiveReducedTorusIso (Y : Cor k) :
    (effectiveMotive k).obj Y ≅
      (Rₑ).obj ((Qₑ).obj (torusCancellationCoefficients k Y)) := by
  let e := cancellationRepresentableReducedDerivedIso k Y
  let d := (effectiveReducedTorusSectionsToDerivedIso k).app
    ((Qₑ).obj (torusCancellationCoefficients k Y))
  exact ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (e ≪≫ d.symm))

/-- The map into the total derived torus sections is the original
representable cancellation map. -/
@[reassoc]
theorem effectiveMotiveReducedTorusIso_hom_inclusion (Y : Cor k) :
    (Vₑ).map (effectiveMotiveReducedTorusIso k Y).hom ≫
        (effectiveReducedTorusSectionsInclusion k).app
          ((Qₑ).obj (torusCancellationCoefficients k Y)) =
      cancellationRepresentableDerivedMap k Y := by
  let P := (Qₑ).obj (torusCancellationCoefficients k Y)
  let e := cancellationRepresentableReducedDerivedIso k Y
  let d := (effectiveReducedTorusSectionsToDerivedIso k).app P
  let i := (reducedTorusSectionsDerivedInclusion k).app ((Vₑ).obj P)
  unfold effectiveMotiveReducedTorusIso effectiveReducedTorusSectionsInclusion
  change (e.hom ≫ d.inv) ≫ d.hom ≫ i = cancellationRepresentableDerivedMap k Y
  rw [Category.assoc, d.inv_hom_id_assoc]
  exact cancellationRepresentableReducedDerivedIso_hom_inclusion k Y

/-- The effective comparison is natural in signed correspondences
between the representing smooth targets. -/
@[reassoc]
theorem effectiveMotiveReducedTorusIso_hom_naturality
    {Y Y' : Cor k} (β : Y ⟶ Y') :
    (effectiveMotive k).map β ≫ (effectiveMotiveReducedTorusIso k Y').hom =
      (effectiveMotiveReducedTorusIso k Y).hom ≫
        (Rₑ).map ((Qₑ).map (torusCancellationCoefficientsMap k β)) := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  let f := (Qₑ).map (torusCancellationCoefficientsMap k β)
  let d := effectiveReducedTorusSectionsToDerivedIso k
  let e := cancellationRepresentableReducedDerivedIso k Y
  let e' := cancellationRepresentableReducedDerivedIso k Y'
  let K := (Qₑ).obj (torusCancellationCoefficients k Y)
  let L := (Qₑ).obj (torusCancellationCoefficients k Y')
  let F := singularSheafCochainFunctor k 0 ⋙ DerivedCategory.Q
  let R := reducedTorusSectionsDerivedFunctor k
  unfold effectiveMotiveReducedTorusIso
  change F.map ((representableLarge k).map β) ≫ (e'.hom ≫ d.inv.app L) =
    (e.hom ≫ d.inv.app K) ≫ (Vₑ).map ((Rₑ).map f)
  calc
    _ = (F.map ((representableLarge k).map β) ≫ e'.hom) ≫ d.inv.app L :=
      (Category.assoc _ _ _).symm
    _ = (e.hom ≫ R.map ((Vₑ).map f)) ≫ d.inv.app L :=
      congrArg (· ≫ d.inv.app L) (cancellationRepresentableReducedDerivedIso_hom_naturality k β)
    _ = e.hom ≫ (R.map ((Vₑ).map f) ≫ d.inv.app L) := Category.assoc _ _ _
    _ = e.hom ≫ (d.inv.app K ≫ (Vₑ).map ((Rₑ).map f)) :=
      congrArg (e.hom ≫ ·) (d.inv.naturality f)
    _ = _ := (Category.assoc _ _ _).symm

end AlgebraicGeometry.MotivicHomotopy
