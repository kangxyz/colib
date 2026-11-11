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
  letI : (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
    (Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  change _ ≫ (Modules.pullback g).map e.hom ≫ (Modules.pullbackUnitIso g).hom = _
  rw [← (Modules.restrictFunctorIsoPullback g).hom.naturality_assoc e.hom]
  exact congrArg (fun m => (Modules.restrictFunctor g).map e.hom ≫ m)
    (Stacks.Modules.restrictFunctorIsoPullback_hom_app_unit_comp_pullbackObjUnitToUnit g)

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
  rw [SectionsEqualizer.pullbackGlobalSections_comp, pullbackCongr_section]

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
  rw [SectionsEqualizer.pullbackGlobalSections_comp, pullbackCongr_section]

/-- At a structure-module automorphism, restriction controls the actual scalar. -/
theorem unitAutomorphism_coordinate_of_restriction {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsOpenImmersion g]
    (E : SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf)
    (e : SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf)
    (hE : (Modules.restrictFunctor g).map E.hom ≫ (Modules.restrictUnitIso g).hom =
      (Modules.restrictUnitIso g).hom ≫ e.hom) :
    g.appTop (E.hom.app ⊤ 1) = e.hom.app ⊤ 1 := by
  letI : (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
    (Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  have he : (Modules.framePullback g E).hom = (Modules.pullbackUnitIso g).hom ≫ e.hom := by
    apply (cancel_epi ((Modules.restrictFunctorIsoPullback g).hom.app _)).1
    rw [restrictComparison_framePullback, hE, ← Category.assoc]
    exact congrArg (fun m => m ≫ e.hom)
      (Stacks.Modules.restrictFunctorIsoPullback_hom_app_unit_comp_pullbackObjUnitToUnit g).symm
  rw [← Modules.framePullback_coordinate, he]
  change e.hom.app ⊤ ((Modules.pullbackUnitIso g).hom.app ⊤
    (pullbackGlobalSections g _ (1 : Γ(Y, ⊤)))) = _
  rw [SectionsEqualizer.pullbackUnitIso_unit, map_one]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
