/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedForgetShift
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.NisnevichDerivedUnit
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionCommShift

/-! # Shift compatibility of the original derived Nisnevich adjunction -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "c" => ComplexShape.up ℤ
local notation "a" => nisnevichSheafify k
local notation "U" => SheafWithTransfers.forget k
local notation "R" => forgetDerivedFunctor k
local notation "Qₚ" => (DerivedCategory.Q : CochainComplex PST ℤ ⥤ DerivedCategory PST)

/-- The canonical abelian structure on transfer sheaves for the Nisnevich derived adjunction. -/
local instance nisnevichAdjunctionShiftAbelian : Abelian NST := SheafWithTransfers.abelian k

/-- The cochain unit identifies the given Nisnevich derived adjunction with the
canonical shift structures of exact sheafification and derived forget. -/
theorem nisnevichDerivedAdjunction_commShift :
    (nisnevichDerivedAdjunction k).CommShift ℤ := by
  let A := (a).mapHomologicalComplex c
  let L := (a).mapDerivedCategory
  let e := (a).mapDerivedCategoryFactors
  let J := (nisnevichSheafificationAdjunction k).mapHomologicalComplexAdjunction c
  let D := nisnevichDerivedAdjunction k
  let d := forgetDerivedUnit k
  let W := HomologicalComplex.quasiIso PST c
  let : NatTrans.CommShift d ℤ := forgetDerivedUnit_commShift k
  let : J.CommShift ℤ := inferInstance
  let : L.IsLeftDerivedFunctor e.hom W := Functor.isLeftDerivedFunctor_of_inverts W L e
  have h (P : CochainComplex PST ℤ) :
      D.unit.app ((Qₚ).obj P) ≫ (R).map (e.hom.app P) =
        (Qₚ).map (J.unit.app P) ≫ d.app (A.obj P) :=
    nisnevichDerivedAdjunction_unit_app_Q_obj k P
  exact Adjunction.commShift_of_isLeftDerivedFunctor J D e.hom d h ℤ W inferInstance

end AlgebraicGeometry.MotivicHomotopy
