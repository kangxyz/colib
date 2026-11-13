/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TatePowerDerivedBond
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TatePowers
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.ReducedShift
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Cancellation
import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedComparison.SingularUnit

/-!
# The original signed integral bond in the reduced derived torus

Cancellation makes the parameter bond on unshifted reduced torus
motives invertible in the native reduced sections. The original
signed map is its shift through the actual localization comparisons.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "J" => effectiveMotivesMinusToDerived k
local notation "C" => singularEffectiveMotiveFunctor k
local notation "R" => effectiveReducedTorusSectionsFunctor k
local notation "N" => reducedTorusSectionsDerivedFunctor k
local notation "B" => torusSectionsDerivedFunctor k
local notation "p" => reducedTorusSectionsDerivedProjection k
local notation "i" => reducedTorusSectionsDerivedInclusion k
local notation "Qₙ" =>
  (DerivedCategory.Q : CochainComplex (LargeSheaves k) ℤ ⥤ DerivedCategory (LargeSheaves k))

/-- Use the canonical abelian structure for the integral coefficient comparison. -/
local instance tatePowerIntegralBondAbelian : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

/-- The unshifted map to the original reduced torus is an isomorphism. -/
theorem isIso_reducedTorusDerivedParameterProduct_projection (q : ℕ) :
    IsIso (reducedTorusDerivedParameterProduct k q ≫
      (p).app ((J).obj ((C).obj (reducedTorus k (q + 1))))) := by
  let X := (C).obj (reducedTorus k q)
  let Y := (C).obj (reducedTorus k (q + 1))
  let η := (effectiveReducedTorusTensorAdjunction k).unit.app X
  let e := (effectiveReducedTorusTensorTorusRetractIso k q).hom
  let d := ((J).obj Y)
  let a := (J).map (η ≫ (R).map e)
  have hι : (effectiveReducedTorusSectionsInclusion k).app Y = (i).app d :=
    effectiveReducedTorusSectionsInclusion_app k Y
  have h : a ≫ (i).app d = reducedTorusDerivedParameterProduct k q := by
    exact (congrArg (a ≫ ·) hι.symm).trans
      (effectiveReducedTorusTensorAdjunction_unit_app_torus k q)
  have ha : (a ≫ (i).app d) ≫ (p).app d = a :=
    (Category.assoc _ _ _).trans <|
    (congrArg (a ≫ ·) (reducedTorusSectionsDerivedInclusion_projection k d)).trans
      (Category.comp_id a)
  have h' : reducedTorusDerivedParameterProduct k q ≫ (p).app d = a :=
    (congrArg (· ≫ (p).app d) h.symm).trans ha
  let : IsIso η := isIso_effectiveReducedTorusTensorAdjunction_unit_app k X
  have hIso : IsIso a := inferInstanceAs (IsIso ((J).map (η ≫ (R).map e)))
  exact h'.symm ▸ hIso

/-- The actual signed integral parameter bond is invertible after its native
projection onto the reduced derived torus. -/
theorem isIso_motivicDerivedReducedTransferParameterProduct (q : ℕ) :
    IsIso (motivicDerivedTransferParameterProduct k q ≫
      (p).app ((Qₙ).obj ((motivicComplex k (q + 1))⟦(1 : ℤ)⟧))) := by
  let K := singularSheafCochainComplex k (reducedTorus k q) 0
  let L₀ := singularSheafCochainComplex k (reducedTorus k (q + 1)) 0
  let s := -(q : ℤ)
  let t := -((q + 1 : ℕ) : ℤ)
  have hs : t + 1 = s := by dsimp [s, t]; omega
  let A := CochainComplex (LargeSheaves k) ℤ
  let x := (shiftFunctorAdd' A t 1 s hs).app L₀
  let D := DerivedCategory (LargeSheaves k)
  let S := shiftFunctor D s
  let X : D := (Qₙ).obj K
  let Y := (Qₙ).obj L₀
  let Y' := (Qₙ).obj ((motivicComplex k (q + 1))⟦(1 : ℤ)⟧)
  let u : X ⟶ (B).obj Y := reducedTorusDerivedParameterProduct k q
  let b := ((Qₙ).commShiftIso s).app K
  let c : S.obj Y ≅ Y' := ((Qₙ).commShiftIso s).symm.app L₀ ≪≫ (Qₙ).mapIso x
  let e : S.obj ((N).obj Y) ≅ (N).obj (S.obj Y) := ((N).commShiftIso s).symm.app Y
  let a : (B).obj (S.obj Y) ≅ S.obj ((B).obj Y) := ((B).commShiftIso s).app Y
  let z := u ≫ (p).app Y
  have hu : z ≫ (i).app Y = u := by
    rw [Category.assoc, reducedTorusSectionsDerivedProjection_inclusion,
      Preadditive.comp_sub]
    have hzero : u ≫ (torusSectionsDerivedUnitRestriction k).app Y = 0 := by
      let P := reducedTorus k (q + 1)
      let A₀ := singularSheafCochainFunctor k 0
      let : A₀.Additive := by
        change (singularSheafCochainFunctor k 0).Additive
        unfold singularSheafCochainFunctor singularCochainFunctor
        infer_instance
      let f := (Qₙ).map (A₀.map (reducedTorusParameterProduct k q))
      let j := singularSheafDerivedTorusSectionsMap k P
      change (f ≫ j) ≫ (torusSectionsDerivedUnitRestriction k).app Y = 0
      change ((Qₙ).map (A₀.map (reducedTorusParameterProduct k q)) ≫ j) ≫
        (torusSectionsDerivedUnitRestriction k).app Y = 0
      rw [Category.assoc, singularSheafDerivedTorusSectionsMap_comp_unit, ← (Qₙ).map_comp,
        ← A₀.map_comp, ← Category.assoc]
      have h : reducedTorusParameterProduct k q ≫ torusUnit P = 0 :=
        reducedTorusParameterProduct_parameterPullback_one k q
      rw [h, zero_comp, A₀.map_zero, (Qₙ).map_zero]
    have hId : u ≫ 𝟙 ((B).obj Y) = u := Category.comp_id u
    rw [hId, ← Category.assoc u, hzero, zero_comp, sub_zero]
  have hi : S.map ((i).app Y) ≫ a.inv = e.hom ≫ (i).app (S.obj Y) := by
    have h : S.map ((i).app Y) = e.hom ≫ (i).app (S.obj Y) ≫ a.hom :=
      (i).shift_app s Y
    exact (congrArg (· ≫ a.inv) h).trans
      (by simp only [Category.assoc, a.hom_inv_id, Category.comp_id])
  have hp : (i).app (S.obj Y) ≫ (B).map c.hom ≫ (p).app Y' = (N).map c.hom := by
    have hn : (i).app (S.obj Y) ≫ (B).map c.hom = (N).map c.hom ≫ (i).app Y' :=
      ((i).naturality c.hom).symm
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (p).app Y') hn).trans
      ((Category.assoc _ _ _).trans
        ((congrArg ((N).map c.hom ≫ ·)
          (reducedTorusSectionsDerivedInclusion_projection k Y')).trans (Category.comp_id _))))
  have h : motivicDerivedTransferParameterProduct k q =
      b.hom ≫ S.map u ≫ a.inv ≫ (B).map c.hom :=
    motivicDerivedTransferParameterProduct_eq_shift k q
  let : IsIso z := isIso_reducedTorusDerivedParameterProduct_projection k q
  have hh : motivicDerivedTransferParameterProduct k q ≫ (p).app Y' =
      b.hom ≫ S.map z ≫ e.hom ≫ (N).map c.hom := by
    calc
      _ = (b.hom ≫ S.map u ≫ a.inv ≫ (B).map c.hom) ≫ (p).app Y' :=
        congrArg (· ≫ (p).app Y') h
      _ = b.hom ≫ S.map z ≫ (S.map ((i).app Y) ≫ a.inv) ≫
          (B).map c.hom ≫ (p).app Y' := by
        rw [← hu, S.map_comp]
        simp only [Category.assoc]
      _ = b.hom ≫ S.map z ≫ (e.hom ≫ (i).app (S.obj Y)) ≫
          (B).map c.hom ≫ (p).app Y' :=
        congrArg (fun g => b.hom ≫ S.map z ≫ g ≫ (B).map c.hom ≫ (p).app Y') hi
      _ = _ := by
        simp only [Category.assoc]
        exact congrArg (fun g => b.hom ≫ S.map z ≫ e.hom ≫ g) hp
  have hIso : IsIso (b.hom ≫ S.map z ≫ e.hom ≫ (N).map c.hom) := inferInstance
  exact hh.symm ▸ hIso

end AlgebraicGeometry.MotivicHomotopy
