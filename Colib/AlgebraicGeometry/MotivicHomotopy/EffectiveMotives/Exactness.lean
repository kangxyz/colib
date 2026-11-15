/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TorusAdjunction
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.ReflectionExactness
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.ReducedTriangulated
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Exactness of the reduced torus adjunction

The actual reduced derived torus functor gives the shift structure on its
left adjoint. The canonical adjunction preserves distinguished triangles.
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
local notation "J" => effectiveMotivesMinusToDerived k
local notation "R" => effectiveReducedTorusSectionsFunctor k
local notation "L" => effectiveReducedTorusTensorFunctor k

/-- Use the abelian structure on Nisnevich sheaves with transfers for the derived adjunctions. -/
local instance : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

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
