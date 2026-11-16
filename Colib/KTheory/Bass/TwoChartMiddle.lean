/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.TwoChartAdditive
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# The original common-corner and signed two-chart middle row

A common coefficient inclusion gives a natural short complex of the original pointwise
chart groups. Natural isomorphisms of coefficient functors induce actual isomorphisms of
these rows. This construction retains both original chart maps and their chosen sign.

Source: `Quillen/KTheory/Bass/TwoChartMiddle.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v w
namespace KTheory.Bass.TwoChart
variable {D : Type u} [Category.{w} D] {P L : D ⥤ D}
variable (c : 𝟭 D ⟶ P) (p m : P ⟶ L) (h : c ≫ p = c ≫ m)

/-- The actual common coefficient map into the two original polynomial groups. -/
def middleCorner (F : D ⥤ AddCommGrpCat.{v}) :
    F ⟶ polynomialDifferenceDiagram p m F ⋙ Arrow.leftFunc where
  app X := biprod.lift (F.map (c.app X)) (F.map (c.app X))
  naturality {X Y} f := by
    have hc := congrArg F.map (c.naturality f)
    apply biprod.hom_ext <;>
      simpa [polynomialDifferenceDiagram, ← Functor.map_comp] using hc

/-- The unchanged signed difference, natural in the base object. -/
def middleDifference (F : D ⥤ AddCommGrpCat.{v}) :
    polynomialDifferenceDiagram p m F ⋙ Arrow.leftFunc ⟶ L ⋙ F where
  app X := polynomialDifference p m F X
  naturality {_ _} f := polynomialDifference_naturality p m F f

include h in
/-- The common coefficient has identical images in the original two Laurent charts. -/
@[reassoc (attr := simp)]
theorem middleCorner_difference (F : D ⥤ AddCommGrpCat.{v}) :
    middleCorner c p m F ≫ middleDifference p m F = 0 := by
  apply NatTrans.ext
  funext X
  change biprod.lift _ _ ≫ biprod.desc _ (-_) = 0
  rw [biprod.lift_desc, Preadditive.comp_neg, ← F.map_comp, ← F.map_comp]
  have hc := NatTrans.congr_app h X
  change c.app X ≫ p.app X = c.app X ≫ m.app X at hc
  rw [hc, add_neg_cancel]

/-- The original three-term natural middle complex, with no asserted exactness. -/
def middleComplex (F : D ⥤ AddCommGrpCat.{v}) : ShortComplex (D ⥤ AddCommGrpCat.{v}) :=
  ShortComplex.mk (middleCorner c p m F) (middleDifference p m F)
    (middleCorner_difference c p m h F)

/-- The original two polynomial groups are identified componentwise by a coefficient isomorphism.
-/
def middlePairIso {F G : D ⥤ AddCommGrpCat.{v}} (e : F ≅ G) :
    polynomialDifferenceDiagram p m F ⋙ Arrow.leftFunc ≅
      polynomialDifferenceDiagram p m G ⋙ Arrow.leftFunc :=
  NatIso.ofComponents (fun X => biprod.mapIso (e.app (P.obj X)) (e.app (P.obj X))) (by
    intro X Y f
    change biprod.map _ _ ≫ biprod.map _ _ = biprod.map _ _ ≫ biprod.map _ _
    apply biprod.hom_ext <;> simp [e.hom.naturality])

/-- Actual natural isomorphisms preserve both original arrows of the middle row. -/
def middleIso {F G : D ⥤ AddCommGrpCat.{v}} (e : F ≅ G) :
    middleComplex c p m h F ≅ middleComplex c p m h G := by
  refine ShortComplex.isoMk e (middlePairIso p m e) (Functor.isoWhiskerLeft L e) ?_ ?_
  · apply NatTrans.ext
    funext X
    change e.hom.app X ≫ biprod.lift _ _ = biprod.lift _ _ ≫ biprod.map _ _
    apply biprod.hom_ext <;>
      simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd, biprod.map_fst,
        biprod.map_snd, biprod.lift_fst_assoc, biprod.lift_snd_assoc]
    · exact (e.hom.naturality (c.app X)).symm
    · exact (e.hom.naturality (c.app X)).symm
  · apply NatTrans.ext
    funext X
    change biprod.map _ _ ≫ biprod.desc _ (-_) = biprod.desc _ (-_) ≫ e.hom.app _
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inl_desc]
      exact (e.hom.naturality (p.app X)).symm
    · simp only [biprod.inr_map_assoc, biprod.inr_desc_assoc, biprod.inr_desc,
        Preadditive.comp_neg, Preadditive.neg_comp]
      exact congrArg Neg.neg (e.hom.naturality (m.app X)).symm

end KTheory.Bass.TwoChart
