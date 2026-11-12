/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.A1Localization
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.ContractionGeometry

import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Contracting the pointed affine-line term of the Tate cone

The literal scheme contraction at one passes through the lifted Yoneda
product and the original pointed cylinder. Its two endpoints give the
constant map at the chosen point and the identity in A¹-localization.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.SmoothSite.Contraction
open CategoryTheory.PointedSimplicialPresheaf

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

local notation "S" => Spec R
local notation "C" => SmoothSite (Spec R)
local notation "J" => SmoothSite.nisnevichTopology (Spec R)
local notation "L" => additiveGroupObject (Spec R)
local notation "I" => affineLineInterval (Spec R)

/-- The original pointed affine line lifted to the coefficient universe. -/
abbrev liftedPointedAffineLine : PointedSimplicialPresheaf.{u + 1} C :=
  (uliftPointed.{u + 1, u} C).obj (pointedAffineLine R)

local notation "X" => liftedPointedAffineLine R

private abbrev liftedLineYoneda : C ⥤ Cᵒᵖ ⥤ SSet.{u + 1} :=
  simplicialYoneda C ⋙ uliftPresheaf.{u + 1, u} C

local notation "F" => liftedLineYoneda R

private def liftedLinePoint (a : base S ⟶ L) :
    (⊤_ (Cᵒᵖ ⥤ SSet.{u + 1})) ⟶ I :=
  (uliftPresheafTerminalIso.{u + 1, u} C).inv ≫
    (uliftPresheaf.{u + 1, u} C).map (representablePoint R a)

/-- The original polynomial evaluation endpoint in the lifted interval. -/
@[no_expose]
def affineLineParameterEndpoint (a : R) : (⊤_ (Cᵒᵖ ⥤ SSet.{u + 1})) ⟶ I :=
  liftedLinePoint R (affineLineParameterPoint R a)

private theorem liftedLineYoneda_map_toBase_point (U : C) (a : base S ⟶ L) :
    (F).map (toBase U ≫ a) = terminal.from ((F).obj U) ≫ liftedLinePoint R a := by
  apply NatTrans.ext
  funext V
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro f
  change ULift.{u + 1} (V.unop ⟶ U) at f
  change ULift.up (f.down ≫ toBase U ≫ a) = ULift.up (toBase V.unop ≫ a)
  exact congrArg (fun g : V.unop ⟶ L => ULift.up g)
    ((Category.assoc f.down (toBase U) a).symm.trans
      (congrArg (· ≫ a) (comp_toBase f.down)))

private def liftedLineProductIso : (F).obj (product L L) ≅ (F).obj L ⨯ (F).obj L := by
  let G := F
  let : PreservesLimit (pair L L) G := by
    dsimp [G, liftedLineYoneda, simplicialYoneda, uliftPresheaf, SSet.uliftFunctor]
    infer_instance
  exact G.mapIso (categoricalProductIso L L).symm ≪≫ PreservesLimitPair.iso G L L

@[reassoc]
private theorem liftedLineProductIso_hom_fst :
    (liftedLineProductIso R).hom ≫ (prod.fst : (F).obj L ⨯ (F).obj L ⟶ (F).obj L) =
      (F).map (productFst L L) := by
  simp only [liftedLineProductIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    PreservesLimitPair.iso_hom, Category.assoc, prodComparison_fst, ← Functor.map_comp,
    categoricalProductIso_inv_fst]

@[reassoc]
private theorem liftedLineProductIso_hom_snd :
    (liftedLineProductIso R).hom ≫ (prod.snd : (F).obj L ⨯ (F).obj L ⟶ (F).obj L) =
      (F).map (productSnd L L) := by
  simp only [liftedLineProductIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    PreservesLimitPair.iso_hom, Category.assoc, prodComparison_snd, ← Functor.map_comp,
    categoricalProductIso_inv_snd]

private theorem liftedLineProductIso_inv_lift {U : C} (f g : U ⟶ L) :
    prod.lift ((F).map f) ((F).map g) ≫ (liftedLineProductIso R).inv =
      (F).map (productLift f g) := by
  apply (cancel_mono (liftedLineProductIso R).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply prod.hom_ext
  · rw [prod.lift_fst, Category.assoc, liftedLineProductIso_hom_fst, ← Functor.map_comp,
      productLift_fst]
  · rw [prod.lift_snd, Category.assoc, liftedLineProductIso_hom_snd, ← Functor.map_comp,
      productLift_snd]

private def affineLineContractionProductMap : (X).right ⨯ I ⟶ (X).right :=
  (liftedLineProductIso R).inv ≫ (F).map (affineLineContractionAtOne R)

private theorem affineLineContractionProductMap_axis :
    intervalAxis X I ≫ affineLineContractionProductMap R =
      terminal.from I ≫ (X).hom := by
  let Y := (F).obj L
  let b : (⊤_ (Cᵒᵖ ⥤ SSet.{u + 1})) ⟶ Y := liftedLinePoint R (affineLineOne R)
  let e := liftedLineProductIso R
  let g := (F).map (affineLineContractionAtOne R)
  change prod.lift (terminal.from Y ≫ b) (𝟙 Y) ≫ (e.inv ≫ g) = terminal.from Y ≫ b
  have ha : (F).map (toBase L ≫ affineLineOne R) = terminal.from Y ≫ b :=
    liftedLineYoneda_map_toBase_point R L (affineLineOne R)
  have hh : prod.lift (terminal.from Y ≫ b) (𝟙 Y) =
      prod.lift ((F).map (toBase L ≫ affineLineOne R)) ((F).map (𝟙 L)) :=
    congrArg₂ prod.lift ha.symm ((F).map_id L).symm
  calc
    _ = (prod.lift ((F).map (toBase L ≫ affineLineOne R)) ((F).map (𝟙 L)) ≫ e.inv) ≫ g :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun h => (h ≫ e.inv) ≫ g) hh)
    _ = (F).map (productLift (toBase L ≫ affineLineOne R) (𝟙 L)) ≫ g :=
      congrArg (· ≫ g) (liftedLineProductIso_inv_lift R (toBase L ≫ affineLineOne R) (𝟙 L))
    _ = (F).map (toBase L ≫ affineLineOne R) := ((F).map_comp _ _).symm.trans
      ((F).congr_map (affineLineContractionAtOne_pointAxis R))
    _ = _ := ha

/-- The native affine-line contraction descended through the actual pointed cylinder. -/
@[no_expose]
def pointedAffineLineContraction : parameterizedCylinder X I ⟶ X :=
  Under.homMk
    (pushout.desc (affineLineContractionProductMap R) (X).hom
      (affineLineContractionProductMap_axis R))
    (pushout.inr_desc _ _ _)

private theorem affineLineContractionProductMap_section (a : R) :
    prod.lift (𝟙 (X).right) (terminal.from (X).right ≫ affineLineParameterEndpoint R a) ≫
        affineLineContractionProductMap R =
      (F).map (nativeAffineSection R L a ≫ affineLineContractionAtOne R) := by
  let Y := (F).obj L
  let b : (⊤_ (Cᵒᵖ ⥤ SSet.{u + 1})) ⟶ Y := affineLineParameterEndpoint R a
  let e := liftedLineProductIso R
  let g := (F).map (affineLineContractionAtOne R)
  change prod.lift (𝟙 Y) (terminal.from Y ≫ b) ≫ (e.inv ≫ g) = _
  have ha : (F).map (toBase L ≫ affineLineParameterPoint R a) = terminal.from Y ≫ b :=
    liftedLineYoneda_map_toBase_point R L (affineLineParameterPoint R a)
  have hh : prod.lift (𝟙 Y) (terminal.from Y ≫ b) =
      prod.lift ((F).map (𝟙 L)) ((F).map (toBase L ≫ affineLineParameterPoint R a)) :=
    congrArg₂ prod.lift ((F).map_id L).symm ha.symm
  have hs : productLift (𝟙 L) (toBase L ≫ affineLineParameterPoint R a) =
      nativeAffineSection R L a := rfl
  calc
    _ = (prod.lift ((F).map (𝟙 L)) ((F).map (toBase L ≫ affineLineParameterPoint R a)) ≫
          e.inv) ≫ g :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun h => (h ≫ e.inv) ≫ g) hh)
    _ = (F).map (productLift (𝟙 L) (toBase L ≫ affineLineParameterPoint R a)) ≫ g :=
      congrArg (· ≫ g)
        (liftedLineProductIso_inv_lift R (𝟙 L) (toBase L ≫ affineLineParameterPoint R a))
    _ = _ := ((F).map_comp _ _).symm.trans
      ((F).congr_map (congrArg (· ≫ affineLineContractionAtOne R) hs))

/-- The zero endpoint is the actual collapse to the chosen point, followed by that point. -/
@[reassoc]
theorem pointedAffineLineContraction_zero :
    cylinderSection X (affineLineParameterEndpoint R 0) ≫ pointedAffineLineContraction R =
      toPoint C X ≫ fromPoint C X := by
  apply Under.UnderMorphism.ext
  change (prod.lift (𝟙 (X).right)
      (terminal.from (X).right ≫ affineLineParameterEndpoint R 0) ≫ pushout.inl _ _) ≫
        pushout.desc (affineLineContractionProductMap R) (X).hom
          (affineLineContractionProductMap_axis R) =
    terminal.from (X).right ≫ liftedLinePoint R (affineLineOne R)
  rw [Category.assoc, pushout.inl_desc, affineLineContractionProductMap_section,
    affineLineContractionAtOne_zero, liftedLineYoneda_map_toBase_point]
  rfl

/-- The one endpoint is the identity of the original pointed line. -/
@[reassoc]
theorem pointedAffineLineContraction_one :
    cylinderSection X (affineLineParameterEndpoint R 1) ≫ pointedAffineLineContraction R = 𝟙 X := by
  apply Under.UnderMorphism.ext
  change (prod.lift (𝟙 (X).right)
      (terminal.from (X).right ≫ affineLineParameterEndpoint R 1) ≫ pushout.inl _ _) ≫
        pushout.desc (affineLineContractionProductMap R) (X).hom
          (affineLineContractionProductMap_axis R) =
    𝟙 (X).right
  rw [Category.assoc, pushout.inl_desc, affineLineContractionProductMap_section,
    affineLineContractionAtOne_one]
  exact (F).map_id L

/-- The original collapse of the affine line pointed at one is an isomorphism
after A¹-localization. -/
theorem isIso_toAffineLineHomotopyCategory_map_pointedAffineLineToPoint :
    IsIso ((toAffineLineHomotopyCategory S).map (toPoint C X)) := by
  let Q := toAffineLineHomotopyCategory S
  let p := toPoint C X
  let s := fromPoint C X
  have h : Q.map (p ≫ s) = Q.map (𝟙 X) := by
    simpa only [pointedAffineLineContraction_zero, pointedAffineLineContraction_one] using
      (toIntervalHomotopyCategory_map_of_cylinder C J I (pointedAffineLineContraction R)
        (affineLineParameterEndpoint R 0) (affineLineParameterEndpoint R 1))
  have hp : Q.map p ≫ Q.map s = 𝟙 _ := by
    rw [← Q.map_comp, h, Q.map_id]
  have hs : Q.map s ≫ Q.map p = 𝟙 _ := by
    rw [← Q.map_comp, show s ≫ p = 𝟙 _ from (point_isZero C).eq_of_tgt _ _, Q.map_id]
  exact ⟨Q.map s, hp, hs⟩

end AlgebraicGeometry.MotivicHomotopy
