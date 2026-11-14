/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.TwoChart

/-!
# Descent through the original double Bass quotient

The composite of the two original Laurent projections is an epimorphism.
A map from the double Laurent group descends uniquely exactly when its four
original chart composites vanish. This uses the actual successive cokernels,
without identifying the two Laurent variables or imposing any swap sign.

Source: `Quillen/KTheory/Bass/TwoChartDoubleDescent.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v w
namespace KTheory.Bass.TwoChart
variable {D : Type u} [Category.{w} D] {P L : D ⥤ D} (p m : P ⟶ L)

/-- The two original Laurent quotient maps in their fixed order. -/
def doubleContractionπ (F : D ⥤ AddCommGrpCat.{v}) (X : D) :
    F.obj (L.obj (L.obj X)) ⟶ (contraction p m (contraction p m F)).obj X :=
  (contractionπ p m F).app (L.obj X) ≫ (contractionπ p m (contraction p m F)).app X

instance doubleContractionπ_epi (F : D ⥤ AddCommGrpCat.{v}) (X : D) :
    Epi (doubleContractionπ p m F X) := by
  unfold doubleContractionπ
  infer_instance

/-- Equality out of the double quotient can be tested on the original Laurent representatives. -/
theorem doubleContraction_hom_ext (F : D ⥤ AddCommGrpCat.{v}) (X : D)
    {A : AddCommGrpCat.{v}} {f g : (contraction p m (contraction p m F)).obj X ⟶ A}
    (h : doubleContractionπ p m F X ≫ f = doubleContractionπ p m F X ≫ g) : f = g :=
  (cancel_epi (doubleContractionπ p m F X)).1 h

/-- The first inner chart vanishes in the double quotient. -/
@[reassoc (attr := simp)]
theorem innerPlus_doubleContractionπ (F : D ⥤ AddCommGrpCat.{v}) (X : D) :
    F.map (p.app (L.obj X)) ≫ doubleContractionπ p m F X = 0 := by
  simp only [doubleContractionπ, plus_contractionπ_assoc, zero_comp]

/-- The second inner chart vanishes in the double quotient. -/
@[reassoc (attr := simp)]
theorem innerMinus_doubleContractionπ (F : D ⥤ AddCommGrpCat.{v}) (X : D) :
    F.map (m.app (L.obj X)) ≫ doubleContractionπ p m F X = 0 := by
  simp only [doubleContractionπ, minus_contractionπ_assoc, zero_comp]

/-- The first outer chart vanishes by naturality of the original first quotient. -/
@[reassoc (attr := simp)]
theorem outerPlus_doubleContractionπ (F : D ⥤ AddCommGrpCat.{v}) (X : D) :
    F.map (L.map (p.app X)) ≫ doubleContractionπ p m F X = 0 := by
  unfold doubleContractionπ
  have hn := (contractionπ p m F).naturality (p.app X)
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, plus_contractionπ, comp_zero]

/-- The second outer chart vanishes by the same actual quotient naturality. -/
@[reassoc (attr := simp)]
theorem outerMinus_doubleContractionπ (F : D ⥤ AddCommGrpCat.{v}) (X : D) :
    F.map (L.map (m.app X)) ≫ doubleContractionπ p m F X = 0 := by
  unfold doubleContractionπ
  have hn := (contractionπ p m F).naturality (m.app X)
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, minus_contractionπ, comp_zero]

/-- Descent through the inner charts preserves a vanishing original outer chart. -/
theorem contractionDescOfCharts_outer_chart (F : D ⥤ AddCommGrpCat.{v}) (X : D)
    {A : AddCommGrpCat.{v}} (f : F.obj (L.obj (L.obj X)) ⟶ A)
    (hp : F.map (p.app (L.obj X)) ≫ f = 0)
    (hm : F.map (m.app (L.obj X)) ≫ f = 0)
    (c : P ⟶ L) (hc : F.map (L.map (c.app X)) ≫ f = 0) :
    (contraction p m F).map (c.app X) ≫
      contractionDescOfCharts p m F (L.obj X) f hp hm = 0 := by
  apply (cancel_epi ((contractionπ p m F).app (P.obj X))).1
  rw [← Category.assoc, ← (contractionπ p m F).naturality (c.app X)]
  simpa only [Functor.comp_map, Category.assoc, contractionπ_descOfCharts,
    comp_zero] using hc

/-- Descent through both fixed cokernels from the four literal chart equations. -/
def doubleContractionDesc (F : D ⥤ AddCommGrpCat.{v}) (X : D)
    {A : AddCommGrpCat.{v}} (f : F.obj (L.obj (L.obj X)) ⟶ A)
    (hip : F.map (p.app (L.obj X)) ≫ f = 0)
    (him : F.map (m.app (L.obj X)) ≫ f = 0)
    (hop : F.map (L.map (p.app X)) ≫ f = 0)
    (hom : F.map (L.map (m.app X)) ≫ f = 0) :
    (contraction p m (contraction p m F)).obj X ⟶ A :=
  contractionDescOfCharts p m (contraction p m F) X
    (contractionDescOfCharts p m F (L.obj X) f hip him)
    (contractionDescOfCharts_outer_chart p m F X f hip him p hop)
    (contractionDescOfCharts_outer_chart p m F X f hip him m hom)

/-- Both actual quotient projections recover the unchanged input map. -/
@[reassoc (attr := simp)]
theorem doubleContractionπ_desc (F : D ⥤ AddCommGrpCat.{v}) (X : D)
    {A : AddCommGrpCat.{v}} (f : F.obj (L.obj (L.obj X)) ⟶ A)
    (hip : F.map (p.app (L.obj X)) ≫ f = 0)
    (him : F.map (m.app (L.obj X)) ≫ f = 0)
    (hop : F.map (L.map (p.app X)) ≫ f = 0)
    (hom : F.map (L.map (m.app X)) ≫ f = 0) :
    doubleContractionπ p m F X ≫ doubleContractionDesc p m F X f hip him hop hom = f := by
  simp only [doubleContractionπ, doubleContractionDesc, Category.assoc,
    contractionπ_descOfCharts]

/-- The double projection is natural in the original coefficient object. -/
@[reassoc]
theorem doubleContractionπ_naturality (F : D ⥤ AddCommGrpCat.{v})
    {X Y : D} (f : X ⟶ Y) :
    F.map (L.map (L.map f)) ≫ doubleContractionπ p m F Y =
      doubleContractionπ p m F X ≫ (contraction p m (contraction p m F)).map f := by
  unfold doubleContractionπ
  have h₁ := (contractionπ p m F).naturality (L.map f)
  have h₂ := (contractionπ p m (contraction p m F)).naturality f
  simp only [Functor.comp_map] at h₁ h₂
  rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

/-- A map of group-valued functors preserves both original quotient projections. -/
@[reassoc]
theorem doubleContractionπ_groupMap {F G : D ⥤ AddCommGrpCat.{v}}
    (α : F ⟶ G) (X : D) :
    doubleContractionπ p m F X ≫
        (contractionMap p m (contractionMap p m α)).app X =
      α.app (L.obj (L.obj X)) ≫ doubleContractionπ p m G X := by
  simp only [doubleContractionπ, Category.assoc, contractionMap_π,
    contractionMap_π_assoc]

end KTheory.Bass.TwoChart
