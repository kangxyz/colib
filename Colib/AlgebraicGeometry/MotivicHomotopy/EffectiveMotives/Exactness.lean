/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TorusAdjunction
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Triangulated
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.ReducedTriangulated
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Exactness of the effective localization and the reduced torus adjunction

The effective inclusion and the actual reduced derived torus functor
give the shift structures on both left adjoints. Their canonical
adjunctions preserve distinguished triangles.
-/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "NST" => LargeSheaves k
local notation "I" => effectiveMotivesMinusInclusion k
local notation "J" => effectiveMotivesMinusToDerived k
local notation "R" => effectiveReducedTorusSectionsFunctor k
local notation "L" => effectiveReducedTorusTensorFunctor k

/-- Use the abelian structure on Nisnevich sheaves with transfers for the derived adjunctions. -/
local instance : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

omit [HasDerivedCategory AddCommGrpCat.{u + 1}] in
instance : (effectiveReflection k).CommShift ℤ :=
  (effectiveReflectionAdjunction k).leftAdjointCommShift ℤ

omit [HasDerivedCategory AddCommGrpCat.{u + 1}] in
instance : (effectiveReflectionAdjunction k).CommShift ℤ :=
  (effectiveReflectionAdjunction k).commShift_of_rightAdjoint ℤ

omit [HasDerivedCategory AddCommGrpCat.{u + 1}] in
instance : (effectiveReflection k).IsTriangulated := by
  let G : DerivedCategory.Minus NST ⥤ EffectiveMotivesMinus k := effectiveReflection k
  let F : EffectiveMotivesMinus k ⥤ DerivedCategory.Minus NST := I
  let h : G ⊣ F := effectiveReflectionAdjunction k
  let : F.IsTriangulated := inferInstanceAs
    (((effectiveCohomologyCondition k).ι).IsTriangulated)
  exact h.isTriangulated_leftAdjoint

omit [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)] in
instance : (R).CommShift ℤ := by
  let F : EffectiveMotivesMinus k ⥤ DerivedCategory NST := J
  let : F.Full := inferInstanceAs
    (((effectiveCohomologyCondition k).ι ⋙ DerivedCategory.Minus.ι).Full)
  let : F.Faithful := inferInstanceAs
    (((effectiveCohomologyCondition k).ι ⋙ DerivedCategory.Minus.ι).Faithful)
  exact Functor.CommShift.ofComp (effectiveReducedTorusSectionsToDerivedIso k) ℤ

omit [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)] in
instance : (R).IsTriangulated := by
  let F : EffectiveMotivesMinus k ⥤ DerivedCategory NST := J
  let N : DerivedCategory NST ⥤ DerivedCategory NST := reducedTorusSectionsDerivedFunctor k
  let : F.Full := inferInstanceAs
    (((effectiveCohomologyCondition k).ι ⋙ DerivedCategory.Minus.ι).Full)
  let : F.Faithful := inferInstanceAs
    (((effectiveCohomologyCondition k).ι ⋙ DerivedCategory.Minus.ι).Faithful)
  let e : (R) ⋙ F ≅ F ⋙ N := effectiveReducedTorusSectionsToDerivedIso k
  let : F.IsTriangulated := inferInstanceAs ((J).IsTriangulated)
  let : N.IsTriangulated := inferInstanceAs ((reducedTorusSectionsDerivedFunctor k).IsTriangulated)
  let : (F ⋙ N).IsTriangulated := inferInstance
  let : (R).CommShift ℤ := Functor.CommShift.ofComp e ℤ
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  exact (Functor.isTriangulated_iff_comp_right e).2 (inferInstanceAs (F ⋙ N).IsTriangulated)

instance : (L).CommShift ℤ :=
  (effectiveReducedTorusTensorAdjunction k).leftAdjointCommShift ℤ

instance : (effectiveReducedTorusTensorAdjunction k).CommShift ℤ :=
  (effectiveReducedTorusTensorAdjunction k).commShift_of_rightAdjoint ℤ

instance : (L).IsTriangulated := by
  let F : EffectiveMotivesMinus k ⥤ EffectiveMotivesMinus k := L
  let G : EffectiveMotivesMinus k ⥤ EffectiveMotivesMinus k := R
  let h : F ⊣ G := effectiveReducedTorusTensorAdjunction k
  let : G.IsTriangulated := inferInstanceAs ((R).IsTriangulated)
  exact h.isTriangulated_leftAdjoint

end AlgebraicGeometry.MotivicHomotopy
