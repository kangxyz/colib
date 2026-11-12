/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.BoundarySectionEquations
public import StacksFrontier.AlgebraicGeometry.IdealOfClosedSubscheme.Basic

/-! # Original full-boundary section normalization descends with the actual frame

The original boundary value-one equations produce the native finite morphism
equations internally. A single descended frame and a single stage recover the
original frame and normalize every original pulled-back section to one.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
universe u v w
namespace AlgebraicGeometry.Scheme.Modules

private theorem normalized_frame_equation_iff {C : Type*} [Category C]
    {R P Q U V : C} (S : P ≅ Q) (e : Q ≅ U) (u : V ≅ U)
    (a : R ⟶ P) (t : R ⟶ V) :
    a ≫ (S ≪≫ e ≪≫ u.symm).hom = t ↔ a ≫ S.hom ≫ e.hom = t ≫ u.hom := by
  constructor
  · intro h
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] using congrArg (fun m => m ≫ u.hom) h
  · intro h
    apply (cancel_mono u.hom).mp
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id] using h

/-- The actual original boundary frame and finitely many value-one section
equations descend together. The equations concern the literal whole boundary,
not its reduction or its closed points. -/
theorem exists_boundary_frame_originalSections_one_of_isLimit
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    (B C : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
    (b : B ⟶ C) (cB : Cone B) (hcB : IsLimit cB)
    [∀ i, CompactSpace (B.obj i)] [∀ i, QuasiSeparatedSpace (B.obj i)]
    (cC : Cone C) (bLim : cB.pt ⟶ cC.pt)
    (hb : ∀ i, cB.π.app i ≫ b.app i = bLim ≫ cC.π.app i)
    (i : I) (M : (C.obj i).Modules) [M.IsFinitePresentation]
    (eLim : (pullback bLim).obj ((pullback (cC.π.app i)).obj M) ≅
      SheafOfModules.unit cB.pt.ringCatSheaf)
    {κ : Type w} [Finite κ] (s : κ → Γ(M, ⊤))
    (hs : ∀ z, Hom.app eLim.hom ⊤
      (pullbackGlobalSections bLim ((pullback (cC.π.app i)).obj M)
        (pullbackGlobalSections (cC.π.app i) M (s z))) = (1 : Γ(cB.pt, ⊤))) :
    ∃ (j : I) (f : j ⟶ i)
      (e : (pullback (b.app j)).obj ((pullback (C.map f)).obj M) ≅
        SheafOfModules.unit (B.obj j).ringCatSheaf),
      ((pullback (cB.π.app j)).map
          ((pullbackSquareIso (B.map f) (b.app i) (b.app j) (C.map f)
            (b.naturality f) M).hom ≫ e.hom) ≫ (pullbackUnitIso (cB.π.app j)).hom =
        canHom (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f)
          ((pullback (b.app i)).obj M) ≫
          (pullbackSquareIso (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M).hom ≫
          eLim.hom) ∧
      ∀ z, Hom.app e.hom ⊤
        (pullbackGlobalSections (b.app j) ((pullback (C.map f)).obj M)
          (pullbackGlobalSections (C.map f) M (s z))) = (1 : Γ(B.obj j, ⊤)) := by
  let P (_ : κ) := SheafOfModules.unit (B.obj i).ringCatSheaf
  let (z : κ) : (P z).IsFinitePresentation := isFinitePresentation_unit (B.obj i)
  let a z := unitHomEquivTop ((pullback (b.app i)).obj M)
    (pullbackGlobalSections (b.app i) M (s z))
  let t (_ : κ) := unitHomEquivTop (SheafOfModules.unit (B.obj i).ringCatSheaf)
    (1 : Γ(B.obj i, ⊤))
  have hat z := (normalized_frame_equation_iff
    (pullbackSquareIso (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M)
    eLim (pullbackUnitIso (cB.π.app i))
    ((pullback (cB.π.app i)).map (a z)) ((pullback (cB.π.app i)).map (t z))).mp
      ((framePullbackIso_originalSection_one_iff
        (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M eLim (s z)).mpr (hs z))
  obtain ⟨j, f, e, he, hst⟩ := exists_boundary_frame_comp_eq_of_isLimit_finite
    B C b cB hcB cC bLim hb i M eLim P a t hat
  refine ⟨j, f, e, he, fun z => ?_⟩
  apply (framePullbackIso_originalSection_one_iff
    (B.map f) (b.app i) (b.app j) (C.map f) (b.naturality f) M e (s z)).mp
  exact (normalized_frame_equation_iff
    (pullbackSquareIso (B.map f) (b.app i) (b.app j) (C.map f) (b.naturality f) M)
    e (pullbackUnitIso (B.map f))
    ((pullback (B.map f)).map (a z)) ((pullback (B.map f)).map (t z))).mpr (hst z)

/-- Transport an original boundary frame through the actual section-model
isomorphism. The original scalar value is unchanged on the entire boundary. -/
theorem originalBoundaryFrame_section_model {X B : Scheme.{u}} (i : B ⟶ X)
    {M N : X.Modules} (E : M ≅ N)
    (e : (pullback i).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (s : Γ(M, ⊤)) (t : Γ(N, ⊤)) (hst : Hom.app E.hom ⊤ s = t) :
    Hom.app ((pullback i).mapIso E.symm ≪≫ e).hom ⊤
      (pullbackGlobalSections i N t) = Hom.app e.hom ⊤ (pullbackGlobalSections i M s) := by
  have hval : Hom.app E.inv ⊤ t = s :=
    (congrArg (Hom.app E.inv ⊤) hst).symm.trans (app_inv_app E ⊤ s)
  change Hom.app e.hom ⊤ (Hom.app ((pullback i).map E.inv) ⊤
    (pullbackGlobalSections i N t)) = _
  exact congrArg (Hom.app e.hom ⊤)
    ((Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality
      i E.inv t).symm.trans (congrArg (pullbackGlobalSections i M) hval))

/-- A specified original limit frame and original sections descend along their
actual section-model identification. The original boundary value-one hypotheses
supply the normalized equations internally; no later frame is supplied. -/
theorem exists_original_boundaryFrame_modeledSections_one_of_isLimit
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    (B C : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
    (b : B ⟶ C) (cB : Cone B) (hcB : IsLimit cB)
    [∀ i, CompactSpace (B.obj i)] [∀ i, QuasiSeparatedSpace (B.obj i)]
    (cC : Cone C) (bLim : cB.pt ⟶ cC.pt)
    (hb : ∀ i, cB.π.app i ≫ b.app i = bLim ≫ cC.π.app i)
    (i : I) (M : (C.obj i).Modules) [M.IsFinitePresentation]
    (N : cC.pt.Modules) (E : N ≅ (pullback (cC.π.app i)).obj M)
    (eOriginal : (pullback bLim).obj N ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    {κ : Type w} [Finite κ] (sOriginal : κ → Γ(N, ⊤)) (s : κ → Γ(M, ⊤))
    (hrecover : ∀ z, Hom.app E.hom ⊤ (sOriginal z) =
      pullbackGlobalSections (cC.π.app i) M (s z))
    (hs : ∀ z, Hom.app eOriginal.hom ⊤ (pullbackGlobalSections bLim N (sOriginal z)) =
      (1 : Γ(cB.pt, ⊤))) :
    let eLim := (pullback bLim).mapIso E.symm ≪≫ eOriginal
    ∃ (j : I) (f : j ⟶ i)
      (e : (pullback (b.app j)).obj ((pullback (C.map f)).obj M) ≅
        SheafOfModules.unit (B.obj j).ringCatSheaf),
      ((pullback (cB.π.app j)).map
          ((pullbackSquareIso (B.map f) (b.app i) (b.app j) (C.map f)
            (b.naturality f) M).hom ≫ e.hom) ≫ (pullbackUnitIso (cB.π.app j)).hom =
        canHom (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f)
          ((pullback (b.app i)).obj M) ≫
          (pullbackSquareIso (cB.π.app i) (b.app i) bLim (cC.π.app i) (hb i) M).hom ≫
          eLim.hom) ∧
      ∀ z, Hom.app e.hom ⊤
        (pullbackGlobalSections (b.app j) ((pullback (C.map f)).obj M)
          (pullbackGlobalSections (C.map f) M (s z))) = (1 : Γ(B.obj j, ⊤)) := by
  dsimp only
  apply exists_boundary_frame_originalSections_one_of_isLimit
    B C b cB hcB cC bLim hb i M ((pullback bLim).mapIso E.symm ≪≫ eOriginal) s
  intro z
  exact (originalBoundaryFrame_section_model bLim E eOriginal
    (sOriginal z) (pullbackGlobalSections (cC.π.app i) M (s z)) (hrecover z)).trans (hs z)

end AlgebraicGeometry.Scheme.Modules
