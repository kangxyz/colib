/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Basic
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.ReducedEffective

/-!
# Reduced right-derived torus sections on effective motives

The actual kernel of derived unit restriction retains the upper bound
and A¹-invariant cohomology of an effective motive.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The actual reduced right-derived torus sections restricted to the
native bounded-above effective motives. -/
def effectiveReducedTorusSectionsFunctor : EffectiveMotivesMinus k ⥤ EffectiveMotivesMinus k := by
  let t := DerivedCategory.TStructure.t (C := SheafWithTransfers.{u + 1} k)
  let F := effectiveMotivesMinusToDerived k ⋙ reducedTorusSectionsDerivedFunctor k
  let G := t.minus.lift F (fun K => by
    obtain ⟨b, hb⟩ := K.obj.property
    let L := (effectiveMotivesMinusToDerived k).obj K
    let : L.IsLE b := hb
    exact ⟨b, reducedTorusSectionsDerived_isLE_of_isLE_of_isA1Invariant k L b K.property⟩)
  refine (effectiveCohomologyCondition k).lift G ?_
  intro K i
  obtain ⟨b, hb⟩ := K.obj.property
  let L := (effectiveMotivesMinusToDerived k).obj K
  let : L.IsLE b := hb
  exact reducedTorusSectionsDerived_homology_isA1Invariant_of_isLE k L b K.property i

/-- Forgetting the effective structure recovers the native derived kernel
functor on the same maps. -/
def effectiveReducedTorusSectionsToDerivedIso :
    effectiveReducedTorusSectionsFunctor k ⋙ effectiveMotivesMinusToDerived k ≅
      effectiveMotivesMinusToDerived k ⋙ reducedTorusSectionsDerivedFunctor k :=
  Iso.refl _

/-- The canonical effective comparison into total derived torus sections
is the inclusion of the original kernel. -/
def effectiveReducedTorusSectionsInclusion :
    effectiveReducedTorusSectionsFunctor k ⋙ effectiveMotivesMinusToDerived k ⟶
      effectiveMotivesMinusToDerived k ⋙ torusSectionsDerivedFunctor k :=
  (effectiveReducedTorusSectionsToDerivedIso k).hom ≫
    Functor.whiskerLeft (effectiveMotivesMinusToDerived k) (reducedTorusSectionsDerivedInclusion k)

@[simp]
theorem effectiveReducedTorusSectionsInclusion_app (K : EffectiveMotivesMinus k) :
    (effectiveReducedTorusSectionsInclusion k).app K =
      (reducedTorusSectionsDerivedInclusion k).app ((effectiveMotivesMinusToDerived k).obj K) :=
  Category.id_comp _

end AlgebraicGeometry.MotivicHomotopy
