/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.DisjointBoundaryGluing
public import Colib.AlgebraicGeometry.Divisors.FrameTransport
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RestrictFreeIsoPullback

/-!
# Literal ring coordinates of the glued whole-boundary frames

Restriction gluing is compared with actual module pullback using the pinned
comparison of the two structure-sheaf maps. Thus the component equations imply
identities of actual regular functions, not merely abstract module morphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- The native open-restriction comparison carries the pulled-back frame to the
literal restriction of the frame. -/
theorem restrictComparison_framePullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] {M : Y.Modules}
    (e : M ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (Modules.restrictFunctorIsoPullback g).hom.app M ≫
        (Modules.framePullback g e).hom =
      (Modules.restrictFunctor g).map e.hom ≫ (Modules.restrictUnitIso g).hom := by
  let : (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
    (Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  change _ ≫ (Modules.pullback g).map e.hom ≫ (Modules.pullbackUnitIso g).hom = _
  have hnat := (Modules.restrictFunctorIsoPullback g).hom.naturality_assoc e.hom
    (Modules.pullbackUnitIso g).hom
  have hunit := Stacks.Modules.restrictFunctorIsoPullback_hom_app_unit_comp_pullbackObjUnitToUnit g
  exact hnat.symm.trans (congrArg (fun m => (Modules.restrictFunctor g).map e.hom ≫ m) hunit)

private theorem pullbackCongr_section {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (M : Y.Modules) (s : Γ(M, ⊤)) :
    ((Modules.pullbackCongr h).app M).hom.app ⊤ (pullbackGlobalSections f M s) =
      pullbackGlobalSections g M s := by
  subst g
  rfl

variable {D Z X : Scheme.{u}} (i : D ⟶ X) (j : Z ⟶ X) (M : X.Modules)
  (E : (Modules.pullback (coprod.desc i j)).obj M ≅
    SheafOfModules.unit (D ⨿ Z).ringCatSheaf)

/-- A glued frame's left coordinate is the literal ring restriction of its
whole-boundary canonical coordinate. -/
theorem boundaryCoprodFrame_inl_coordinate
    (e : (Modules.pullback i).obj M ≅ SheafOfModules.unit D.ringCatSheaf)
    (hE : (Modules.restrictFunctor (coprod.inl : D ⟶ D ⨿ Z)).map E.hom ≫
        (Modules.restrictUnitIso _).hom =
      (boundaryCoprodRestrictLeft i j).hom.app M ≫ e.hom) (s : Γ(M, ⊤)) :
    (coprod.inl : D ⟶ D ⨿ Z).appTop
      (E.hom.app ⊤ (pullbackGlobalSections (coprod.desc i j) M s)) =
        e.hom.app ⊤ (pullbackGlobalSections i M s) := by
  let a := (Modules.pullbackComp (coprod.inl : D ⟶ D ⨿ Z) (coprod.desc i j)).app M ≪≫
    (Modules.pullbackCongr (coprod.inl_desc i j)).app M
  have he : (Modules.framePullback (coprod.inl : D ⟶ D ⨿ Z) E).hom = a.hom ≫ e.hom := by
    apply (cancel_epi ((Modules.restrictFunctorIsoPullback
      (coprod.inl : D ⟶ D ⨿ Z)).hom.app _)).1
    rw [restrictComparison_framePullback, hE]
    rfl
  rw [← Modules.framePullback_coordinate, he]
  change e.hom.app ⊤
    (((Modules.pullbackCongr (coprod.inl_desc i j)).app M).hom.app ⊤
      (((Modules.pullbackComp (coprod.inl : D ⟶ D ⨿ Z) (coprod.desc i j)).app M).hom.app ⊤
        (pullbackGlobalSections (coprod.inl : D ⟶ D ⨿ Z) _
          (pullbackGlobalSections (coprod.desc i j) M s)))) = _
  have hc := SectionsEqualizer.pullbackGlobalSections_comp
    (coprod.inl : D ⟶ D ⨿ Z) (coprod.desc i j) M s
  have hd := pullbackCongr_section (coprod.inl_desc i j) M s
  have h := congrArg (fun t => ((Modules.pullbackCongr (coprod.inl_desc i j)).app M).hom.app ⊤ t) hc
  exact congrArg (fun t => e.hom.app ⊤ t) (h.trans hd)

/-- The marked coordinate retains the entire right summand, including all its
nilpotents and all its points. -/
theorem boundaryCoprodFrame_inr_coordinate
    (e : (Modules.pullback j).obj M ≅ SheafOfModules.unit Z.ringCatSheaf)
    (hE : (Modules.restrictFunctor (coprod.inr : Z ⟶ D ⨿ Z)).map E.hom ≫
        (Modules.restrictUnitIso _).hom =
      (boundaryCoprodRestrictRight i j).hom.app M ≫ e.hom) (s : Γ(M, ⊤)) :
    (coprod.inr : Z ⟶ D ⨿ Z).appTop
      (E.hom.app ⊤ (pullbackGlobalSections (coprod.desc i j) M s)) =
        e.hom.app ⊤ (pullbackGlobalSections j M s) := by
  let a := (Modules.pullbackComp (coprod.inr : Z ⟶ D ⨿ Z) (coprod.desc i j)).app M ≪≫
    (Modules.pullbackCongr (coprod.inr_desc i j)).app M
  have he : (Modules.framePullback (coprod.inr : Z ⟶ D ⨿ Z) E).hom = a.hom ≫ e.hom := by
    apply (cancel_epi ((Modules.restrictFunctorIsoPullback
      (coprod.inr : Z ⟶ D ⨿ Z)).hom.app _)).1
    rw [restrictComparison_framePullback, hE]
    rfl
  rw [← Modules.framePullback_coordinate, he]
  change e.hom.app ⊤
    (((Modules.pullbackCongr (coprod.inr_desc i j)).app M).hom.app ⊤
      (((Modules.pullbackComp (coprod.inr : Z ⟶ D ⨿ Z) (coprod.desc i j)).app M).hom.app ⊤
        (pullbackGlobalSections (coprod.inr : Z ⟶ D ⨿ Z) _
          (pullbackGlobalSections (coprod.desc i j) M s)))) = _
  have hc := SectionsEqualizer.pullbackGlobalSections_comp
    (coprod.inr : Z ⟶ D ⨿ Z) (coprod.desc i j) M s
  have hd := pullbackCongr_section (coprod.inr_desc i j) M s
  have h := congrArg (fun t => ((Modules.pullbackCongr (coprod.inr_desc i j)).app M).hom.app ⊤ t) hc
  exact congrArg (fun t => e.hom.app ⊤ t) (h.trans hd)

/-- At a structure-module automorphism, restriction controls the actual scalar. -/
theorem unitAutomorphism_coordinate_of_restriction {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsOpenImmersion g]
    (E : SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf)
    (e : SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf)
    (hE : (Modules.restrictFunctor g).map E.hom ≫ (Modules.restrictUnitIso g).hom =
      (Modules.restrictUnitIso g).hom ≫ e.hom) :
    g.appTop (Modules.Hom.app E.hom ⊤ (1 : Γ(Y, ⊤))) =
      Modules.Hom.app e.hom ⊤ (1 : Γ(X, ⊤)) := by
  let : (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
    (Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  have hunit := Stacks.Modules.restrictFunctorIsoPullback_hom_app_unit_comp_pullbackObjUnitToUnit g
  have he : (Modules.framePullback g E).hom = (Modules.pullbackUnitIso g).hom ≫ e.hom := by
    apply (cancel_epi ((Modules.restrictFunctorIsoPullback g).hom.app _)).1
    exact (restrictComparison_framePullback g E).trans
      (hE.trans ((congrArg (fun m => m ≫ e.hom) hunit.symm).trans (Category.assoc _ _ _)))
  have hframe := Modules.framePullback_coordinate g E (1 : Γ(Y, ⊤))
  have happ := congrArg (fun m => Modules.Hom.app m ⊤
    (pullbackGlobalSections g (SheafOfModules.unit Y.ringCatSheaf) (1 : Γ(Y, ⊤)))) he
  have hp := (SectionsEqualizer.pullbackUnitIso_unit g (1 : Γ(Y, ⊤))).trans
    (map_one g.appTop.hom)
  exact hframe.symm.trans (happ.trans (congrArg (fun t => Modules.Hom.app e.hom ⊤ t) hp))

end AlgebraicGeometry.Scheme.RelativeCurvePencil
