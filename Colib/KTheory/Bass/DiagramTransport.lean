/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Bass.TwoChart

/-!
Source: `Quillen/KTheory/Bass/DiagramTransport.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

Transport of the actual two-chart Bass cokernel along genuine natural diagram isomorphisms. The full
difference arrow, cokernel isomorphism and original Laurent representative square are constructed,
with independent category and group universes.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u₁ u₂ v₁ v₂ w
namespace KTheory.Bass.TwoChart
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {P L : C ⥤ C} {P' L' : D ⥤ D} (p m : P ⟶ L) (p' m' : P' ⟶ L')
variable (T : D ⥤ C) (eP : P' ⋙ T ≅ T ⋙ P) (eL : L' ⋙ T ≅ T ⋙ L)
variable (hp : ∀ X, T.map (p'.app X) ≫ eL.hom.app X = eP.hom.app X ≫ p.app (T.obj X))
variable (hm : ∀ X, T.map (m'.app X) ≫ eL.hom.app X = eP.hom.app X ≫ m.app (T.obj X))

/-- A genuine natural chart identification gives the actual isomorphism of difference arrows. -/
def transportDifferenceIso (F : C ⥤ AddCommGrpCat.{w}) :
    polynomialDifferenceDiagram p' m' (T ⋙ F) ≅ T ⋙ polynomialDifferenceDiagram p m F :=
  NatIso.ofComponents (fun X ↦ Arrow.isoMk
    (biprod.mapIso (F.mapIso (eP.app X)) (F.mapIso (eP.app X))) (F.mapIso (eL.app X)) (by
      change biprod.map (F.map (eP.hom.app X)) (F.map (eP.hom.app X)) ≫
        polynomialDifference p m F (T.obj X) =
          polynomialDifference p' m' (T ⋙ F) X ≫ F.map (eL.hom.app X)
      apply biprod.hom_ext'
      · simp only [biprod.inl_map_assoc,polynomialDifference,biprod.inl_desc_assoc,
          Functor.comp_map,biprod.inl_desc,← F.map_comp]
        exact congrArg F.map (hp X).symm
      · simp only [biprod.inr_map_assoc,polynomialDifference,biprod.inr_desc_assoc,
          Functor.comp_map,biprod.inr_desc,Preadditive.comp_neg,
          Preadditive.neg_comp,← F.map_comp]
        exact congrArg (fun f ↦ -F.map f) (hm X).symm)) (by
      intro X Y f
      apply Arrow.hom_ext
      · change biprod.map (F.map (T.map (P'.map f))) (F.map (T.map (P'.map f))) ≫
          biprod.map (F.map (eP.hom.app Y)) (F.map (eP.hom.app Y)) =
            biprod.map (F.map (eP.hom.app X)) (F.map (eP.hom.app X)) ≫
              biprod.map (F.map (P.map (T.map f))) (F.map (P.map (T.map f)))
        have h : F.map (T.map (P'.map f)) ≫ F.map (eP.hom.app Y) =
            F.map (eP.hom.app X) ≫ F.map (P.map (T.map f)) := by
          simpa only [← F.map_comp,Functor.comp_map] using congrArg F.map (eP.hom.naturality f)
        dsimp only [Functor.comp_obj] at *
        apply biprod.hom_ext
        · simp only [Category.assoc,biprod.map_fst,biprod.map_fst_assoc]
          exact congrArg (fun g ↦ (biprod.fst : F.obj (T.obj (P'.obj X)) ⊞
            F.obj (T.obj (P'.obj X)) ⟶ _) ≫ g) h
        · simp only [Category.assoc,biprod.map_snd,biprod.map_snd_assoc]
          exact congrArg (fun g ↦ (biprod.snd : F.obj (T.obj (P'.obj X)) ⊞
            F.obj (T.obj (P'.obj X)) ⟶ _) ≫ g) h
      · change F.map (T.map (L'.map f)) ≫ F.map (eL.hom.app Y) =
          F.map (eL.hom.app X) ≫ F.map (L.map (T.map f))
        simpa only [← F.map_comp,Functor.comp_map] using congrArg F.map (eL.hom.naturality f))

/-- Actual cokernel transport along the proved chart squares. -/
def contractionTransportIso (F : C ⥤ AddCommGrpCat.{w}) :
    contraction p' m' (T ⋙ F) ≅ T ⋙ contraction p m F :=
  Functor.isoWhiskerRight (transportDifferenceIso p m p' m' T eP eL hp hm F) (coker AddCommGrpCat)

/-- The original Laurent representative map is preserved by the transported cokernel isomorphism. -/
@[reassoc (attr := simp)] lemma contractionTransportIso_π (F : C ⥤ AddCommGrpCat.{w}) (X : D) :
    (contractionπ p' m' (T ⋙ F)).app X ≫
      (contractionTransportIso p m p' m' T eP eL hp hm F).hom.app X =
    F.map (eL.hom.app X) ≫ (contractionπ p m F).app (T.obj X) := by
  simp
    [contractionTransportIso,transportDifferenceIso,contractionπ,coker,polynomialDifferenceDiagram]

end KTheory.Bass.TwoChart

end
