/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.TwoChartMiddle

/-!
# The original pointwise polynomial pair as a natural biproduct

The original chart-pair functor is the binary biproduct of the two polynomial coefficient
functors. The comparison retains the literal projections and inclusions, so it can be used
under additive contraction without treating chosen functor-category limits as definitional.

Source: `Quillen/KTheory/Bass/TwoChartMiddleBiproduct.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v w
namespace KTheory.Bass.TwoChart
variable {D : Type u} [Category.{w} D] {P L : D ⥤ D} (p m : P ⟶ L)

/-- The two actual polynomial groups, with their literal pointwise split projections. -/
def polynomialPairBicone (F : D ⥤ AddCommGrpCat.{v}) : BinaryBicone (P ⋙ F) (P ⋙ F) where
  pt := polynomialDifferenceDiagram p m F ⋙ Arrow.leftFunc
  fst :=
    { app := fun _ => biprod.fst
      naturality := fun {_ _} _ => biprod.map_fst _ _ }
  snd :=
    { app := fun _ => biprod.snd
      naturality := fun {_ _} _ => biprod.map_snd _ _ }
  inl :=
    { app := fun _ => biprod.inl
      naturality := fun {_ _} _ => (biprod.inl_map _ _).symm }
  inr :=
    { app := fun _ => biprod.inr
      naturality := fun {_ _} _ => (biprod.inr_map _ _).symm }
  inl_fst := by apply NatTrans.ext; funext X; exact biprod.inl_fst
  inl_snd := by apply NatTrans.ext; funext X; exact biprod.inl_snd
  inr_fst := by apply NatTrans.ext; funext X; exact biprod.inr_fst
  inr_snd := by apply NatTrans.ext; funext X; exact biprod.inr_snd

/-- The original pointwise pair satisfies the full natural biproduct identity. -/
def polynomialPairBiconeIsBilimit (F : D ⥤ AddCommGrpCat.{v}) :
    (polynomialPairBicone p m F).IsBilimit :=
  isBinaryBilimitOfTotal _ (by
    apply NatTrans.ext
    funext X
    exact biprod.total)

/-- The canonical biproduct comparison, with unchanged pointwise projections and inclusions. -/
def polynomialPairBiprodIso (F : D ⥤ AddCommGrpCat.{v}) :
    polynomialDifferenceDiagram p m F ⋙ Arrow.leftFunc ≅ (P ⋙ F) ⊞ (P ⋙ F) :=
  biprod.uniqueUpToIso _ _ (polynomialPairBiconeIsBilimit p m F)

/-- The original first projection is retained by the chosen natural biproduct comparison. -/
@[reassoc (attr := simp)]
theorem polynomialPairBiprodIso_hom_fst (F : D ⥤ AddCommGrpCat.{v}) :
    (polynomialPairBiprodIso p m F).hom ≫ biprod.fst = (polynomialPairBicone p m F).fst :=
  biprod.lift_fst _ _

/-- The original second projection is retained by the same comparison. -/
@[reassoc (attr := simp)]
theorem polynomialPairBiprodIso_hom_snd (F : D ⥤ AddCommGrpCat.{v}) :
    (polynomialPairBiprodIso p m F).hom ≫ biprod.snd = (polynomialPairBicone p m F).snd :=
  biprod.lift_snd _ _

end KTheory.Bass.TwoChart
