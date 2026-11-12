/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryRootTransport
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.SectionModelRefinement

/-! # Original boundary frame recovery as an actual square-pullback identity

The native canHom recovery equation for a descended frame identifies its actual
pullback with the original frame after the prescribed canonical module comparison.
This retains the same frame and original model through a further stage.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
universe u v
namespace AlgebraicGeometry.Scheme.Modules

private theorem frame_recovery_aux {C : Type*} [Category C] {A B D E F U : C}
    (S : A ≅ B) (T : B ≅ D) (K : D ≅ E) (R : A ≅ F) (V : F ≅ E)
    (N : B ⟶ U) (e : E ≅ U) (hSquare : R ≪≫ V = S ≪≫ T ≪≫ K)
    (hrec : S.hom ≫ N = R.hom ≫ V.hom ≫ e.hom) :
    T.inv ≫ N = K.hom ≫ e.hom := by
  have h : N = T.hom ≫ K.hom ≫ e.hom := by
    apply (cancel_epi S.hom).mp
    have H := congrArg (fun z => z ≫ e.hom) (congrArg Iso.hom hSquare)
    exact hrec.trans (by simpa only [Iso.trans_hom, Category.assoc] using H)
  rw [h]
  simp only [Iso.inv_hom_id_assoc]

/-- The actual descended frame pulls back to the original frame under precisely
the same canonical module comparison as the descended sections. -/
theorem boundaryFrame_recovery_pullback {I : Type u} [Category.{v} I]
    (B C : I ⥤ Scheme.{u}) (b : B ⟶ C) (cB : Cone B) (cC : Cone C)
    (bLim : cB.pt ⟶ cC.pt)
    (hb : ∀ i, cB.π.app i ≫ b.app i = bLim ≫ cC.π.app i)
    {i j : I} (f : j ⟶ i) (M : (C.obj i).Modules)
    (eLim : (pullback bLim).obj ((pullback (cC.π.app i)).obj M) ≅
      SheafOfModules.unit cB.pt.ringCatSheaf)
    (e : (pullback (b.app j)).obj ((pullback (C.map f)).obj M) ≅
      SheafOfModules.unit (B.obj j).ringCatSheaf)
    (he : (pullback (cB.π.app j)).map
          ((pullbackSquareIso (B.map f) (b.app i) (b.app j) (C.map f)
            (b.naturality f) M).hom ≫ e.hom) ≫ (pullbackUnitIso (cB.π.app j)).hom =
        canHom (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f)
          ((pullback (b.app i)).obj M) ≫
          (pullbackSquareIso (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M).hom ≫
          eLim.hom) :
    pullbackBoundaryTrivialization (cB.π.app j) (b.app j) bLim (cC.π.app j) (hb j)
        ((pullback (C.map f)).obj M) e =
      (pullback bLim).mapIso (canIso (cC.π.app j) (C.map f) (cC.π.app i) (cC.w f) M) ≪≫ eLim := by
  apply Iso.ext
  apply frame_recovery_aux
    ((pullback (cB.π.app j)).mapIso
      (pullbackSquareIso (B.map f) (b.app i) (b.app j) (C.map f) (b.naturality f) M))
    (pullbackSquareIso (cB.π.app j) (b.app j) bLim (cC.π.app j) (hb j)
      ((pullback (C.map f)).obj M))
    ((pullback bLim).mapIso (canIso (cC.π.app j) (C.map f) (cC.π.app i) (cC.w f) M))
    (canIso (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f) ((pullback (b.app i)).obj M))
    (pullbackSquareIso (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M)
  · exact pullbackSquareIso_comp (cB.π.app j) (B.map f) (cB.π.app i)
      bLim (b.app j) (b.app i) (cC.π.app j) (C.map f) (cC.π.app i)
      (cB.w f) (cC.w f) (hb j) (b.naturality f) (hb i) M
  · have H := (pullback (cB.π.app j)).map_comp
      (pullbackSquareIso (B.map f) (b.app i) (b.app j) (C.map f) (b.naturality f) M).hom e.hom
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (pullbackUnitIso (cB.π.app j)).hom) H.symm).trans he)

private theorem model_frame_refine {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {N P Q : C} {U : D} (E : N ≅ P) (c : Q ≅ P) (e : F.obj N ≅ U) :
    F.mapIso c ≪≫ (F.mapIso E.symm ≪≫ e) = F.mapIso (E ≪≫ c.symm).symm ≪≫ e := by
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Functor.mapIso_trans, Iso.trans_assoc]

/-- The descended boundary frame recovers the specified original frame through
exactly the same refined original module model as the descended section. -/
theorem boundaryFrame_originalModel_recovery {I : Type u} [Category.{v} I]
    (B C : I ⥤ Scheme.{u}) (b : B ⟶ C) (cB : Cone B) (cC : Cone C)
    (bLim : cB.pt ⟶ cC.pt)
    (hb : ∀ i, cB.π.app i ≫ b.app i = bLim ≫ cC.π.app i)
    {i j : I} (f : j ⟶ i) (M : (C.obj i).Modules)
    (N : cC.pt.Modules) (E : N ≅ (pullback (cC.π.app i)).obj M)
    (eOriginal : (pullback bLim).obj N ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    (e : (pullback (b.app j)).obj ((pullback (C.map f)).obj M) ≅
      SheafOfModules.unit (B.obj j).ringCatSheaf)
    (he : (pullback (cB.π.app j)).map
          ((pullbackSquareIso (B.map f) (b.app i) (b.app j) (C.map f)
            (b.naturality f) M).hom ≫ e.hom) ≫ (pullbackUnitIso (cB.π.app j)).hom =
        canHom (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f)
          ((pullback (b.app i)).obj M) ≫
          (pullbackSquareIso (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M).hom ≫
          ((pullback bLim).mapIso E.symm ≪≫ eOriginal).hom) :
    pullbackBoundaryTrivialization (cB.π.app j) (b.app j) bLim (cC.π.app j) (hb j)
        ((pullback (C.map f)).obj M) e =
      (pullback bLim).mapIso
        (refinedSectionModelIso (cC.π.app j) (C.map f) (cC.π.app i) (cC.w f) M E).symm ≪≫
        eOriginal := by
  exact (boundaryFrame_recovery_pullback B C b cB cC bLim hb f M
    ((pullback bLim).mapIso E.symm ≪≫ eOriginal) e he).trans
      (model_frame_refine (pullback bLim) E
        (canIso (cC.π.app j) (C.map f) (cC.π.app i) (cC.w f) M) eOriginal)

end AlgebraicGeometry.Scheme.Modules
