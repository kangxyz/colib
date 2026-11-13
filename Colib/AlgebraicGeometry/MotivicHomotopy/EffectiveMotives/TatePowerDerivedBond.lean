/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.TransferParameterShiftMap
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TatePowerUnit
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.UnitShift

/-!
# The signed derived parameter bond

The integral motivic parameter map localizes and then applies the
original torus-derived comparison. Its signed shift is the shift
of the corresponding parameter map on singular effective motives.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

local notation "B" => torusSectionsFunctor k
local notation "R" => torusSectionsDerivedFunctor k
local notation "η" => torusSectionsDerivedUnit k
local notation "Qₙ" => DerivedCategory.Q (C := LargeSheaves k)

/-- Use the canonical abelian structure for the derived signed bond. -/
local instance tatePowerDerivedBondAbelian : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

/-- The actual signed integral parameter bond after passing to derived
Nisnevich transfer sheaves. -/
def motivicDerivedTransferParameterProduct (q : ℕ) :
    (Qₙ).obj (motivicComplex k q) ⟶
      (R).obj ((Qₙ).obj ((motivicComplex k (q + 1))⟦(1 : ℤ)⟧)) :=
  (Qₙ).map (motivicTransferParameterProduct k q) ≫
    (η).app ((motivicComplex k (q + 1))⟦(1 : ℤ)⟧)

private theorem localizedShiftTorusParameterMap
    {K L : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ}
    (s t : ℤ) (h : t + 1 = s)
    (f : K ⟶ ((B).mapHomologicalComplex (.up ℤ)).obj L) :
    let C := CochainComplex (SheafWithTransfers.{u + 1} k) ℤ
    let x := (shiftFunctorAdd' C t 1 s h).hom.app L
    (Qₙ).map (shiftTorusParameterMap k s t h f) ≫ (η).app (L⟦t⟧⟦(1 : ℤ)⟧) =
      ((Qₙ).commShiftIso s).hom.app K ≫
        (shiftFunctor _ s).map ((Qₙ).map f ≫ (η).app L) ≫
        ((R).commShiftIso s).inv.app ((Qₙ).obj L) ≫
        (R).map (((Qₙ).commShiftIso s).inv.app L ≫ (Qₙ).map x) := by
  intro C x
  let A := SheafWithTransfers.{u + 1} k
  let S := shiftFunctor (DerivedCategory A) s
  let W := shiftFunctor (CochainComplex A ℤ) s
  let T := (B).mapHomologicalComplex (.up ℤ)
  let a := (T.commShiftIso s).app L
  let b := ((Qₙ).commShiftIso s).app L
  let c := ((Qₙ).commShiftIso s).app (T.obj L)
  let d := ((R).commShiftIso s).app ((Qₙ).obj L)
  let e := ((Qₙ).commShiftIso s).app K
  have hu : (η).app (L⟦s⟧) ≫ (R).map b.hom ≫ d.hom =
      (Qₙ).map a.hom ≫ c.hom ≫ S.map ((η).app L) := by
    have hh := NatTrans.shift_app_comm (η) s L
    change ((T ⋙ (Qₙ)).commShiftIso s).hom.app L ≫ S.map ((η).app L) =
      (η).app (L⟦s⟧) ≫ (((Qₙ) ⋙ R).commShiftIso s).hom.app L at hh
    rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at hh
    exact hh.symm.trans (Category.assoc _ _ _)
  have hv : (Qₙ).map a.inv ≫ (η).app (L⟦s⟧) =
      c.hom ≫ S.map ((η).app L) ≫ d.inv ≫ (R).map b.inv := by
    let p : (R).obj ((Qₙ).obj (L⟦s⟧)) ⟶ S.obj ((R).obj ((Qₙ).obj L)) :=
      (R).map b.hom ≫ d.hom
    let : IsIso p := inferInstanceAs (IsIso ((R).map b.hom ≫ d.hom))
    apply (cancel_mono p).1
    change ((Qₙ).map a.inv ≫ (η).app (L⟦s⟧)) ≫ ((R).map b.hom ≫ d.hom) =
      (c.hom ≫ S.map ((η).app L) ≫ d.inv ≫ (R).map b.inv) ≫ ((R).map b.hom ≫ d.hom)
    calc
      _ = (Qₙ).map a.inv ≫ ((η).app (L⟦s⟧) ≫ (R).map b.hom ≫ d.hom) :=
        Category.assoc _ _ _
      _ = ((Qₙ).map a.inv ≫ (Qₙ).map a.hom) ≫ c.hom ≫ S.map ((η).app L) := by
        rw [hu]
        simp only [Category.assoc]
      _ = c.hom ≫ S.map ((η).app L) := by
        rw [← (Qₙ).map_comp, a.inv_hom_id, (Qₙ).map_id, Category.id_comp]
      _ = _ := by
        symm
        simp only [Category.assoc, ← (R).map_comp_assoc, b.inv_hom_id]
        have hId : (R).map (𝟙 (S.obj ((Qₙ).obj L))) = 𝟙 _ :=
          (R).map_id (S.obj ((Qₙ).obj L))
        have hinner : d.inv ≫ (R).map (𝟙 (S.obj ((Qₙ).obj L))) ≫ d.hom = 𝟙 _ :=
          (congrArg (fun f => d.inv ≫ f ≫ d.hom) hId).trans
            ((congrArg (d.inv ≫ ·) (Category.id_comp d.hom)).trans d.inv_hom_id)
        exact (congrArg (fun f => c.hom ≫ S.map ((η).app L) ≫ f) hinner).trans
          (congrArg (c.hom ≫ ·) (Category.comp_id _))
  have hf : (Qₙ).map (W.map f) ≫ c.hom = e.hom ≫ S.map ((Qₙ).map f) :=
    ((Qₙ).commShiftIso s).hom.naturality f
  have hx : (Qₙ).map (T.map x) ≫ (η).app (L⟦t⟧⟦(1 : ℤ)⟧) =
      (η).app (L⟦s⟧) ≫ (R).map ((Qₙ).map x) := (η).naturality x
  change (Qₙ).map (W.map f ≫ a.inv ≫ T.map x) ≫ (η).app _ = _
  calc
    _ = (Qₙ).map (W.map f) ≫ ((Qₙ).map a.inv ≫ (η).app (L⟦s⟧)) ≫
        (R).map ((Qₙ).map x) := by
      simp only [(Qₙ).map_comp, Category.assoc]
      exact congrArg (fun z => (Qₙ).map (W.map f) ≫ (Qₙ).map a.inv ≫ z) hx
    _ = e.hom ≫ S.map ((Qₙ).map f) ≫ S.map ((η).app L) ≫ d.inv ≫
        (R).map b.inv ≫ (R).map ((Qₙ).map x) := by
      rw [hv]
      simp only [Category.assoc, reassoc_of% hf]
    _ = _ := by
      rw [← S.map_comp_assoc, ← (R).map_comp]
      rfl

/-- The signed derived bond is the shift of the actual unshifted
parameter map through the native localization comparisons. -/
theorem motivicDerivedTransferParameterProduct_eq_shift (q : ℕ) :
    let K := singularSheafCochainComplex k (reducedTorus k q) 0
    let L := singularSheafCochainComplex k (reducedTorus k (q + 1)) 0
    let s := -(q : ℤ)
    let t := -((q + 1 : ℕ) : ℤ)
    let h : t + 1 = s := by dsimp [s, t]; omega
    let C := CochainComplex (SheafWithTransfers.{u + 1} k) ℤ
    let x := (shiftFunctorAdd' C t 1 s h).hom.app L
    motivicDerivedTransferParameterProduct k q =
      ((Qₙ).commShiftIso s).hom.app K ≫
        (shiftFunctor _ s).map (reducedTorusDerivedParameterProduct k q) ≫
        ((R).commShiftIso s).inv.app ((Qₙ).obj L) ≫
        (R).map (((Qₙ).commShiftIso s).inv.app L ≫ (Qₙ).map x) := by
  intro K L s t h C x
  let f := (singularSheafCochainFunctor k 0).map (reducedTorusParameterProduct k q) ≫
    singularSheafCochainTorusSectionsMap k (reducedTorus k (q + 1))
  have hf : (Qₙ).map f ≫ (η).app L = reducedTorusDerivedParameterProduct k q := by
    unfold reducedTorusDerivedParameterProduct singularSheafDerivedTorusSectionsMap
    simp only [f, Category.assoc, (Qₙ).map_comp]
    rfl
  have hg : motivicTransferParameterProduct k q = shiftTorusParameterMap k s t h f :=
    motivicTransferParameterProduct_eq_shiftTorusParameterMap k q
  unfold motivicDerivedTransferParameterProduct
  rw [hg]
  exact (localizedShiftTorusParameterMap k s t h f).trans
    (congrArg (fun a => ((Qₙ).commShiftIso s).hom.app K ≫ (shiftFunctor _ s).map a ≫
      ((R).commShiftIso s).inv.app ((Qₙ).obj L) ≫
      (R).map (((Qₙ).commShiftIso s).inv.app L ≫ (Qₙ).map x)) hf)

end AlgebraicGeometry.MotivicHomotopy
