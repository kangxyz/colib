/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.BoundarySectionFrames
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.SectionModelRefinement
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.ZeroSchemeCartesian

/-! # The original auxiliary frame descends without losing the selected finite pair

Refine a selected actual finite pair once to descend the original denominator
frame. Both original section identifications and both whole finite locally free
zero schemes are retained on that same refinement.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
universe u v
namespace AlgebraicGeometry.Scheme.Modules

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property ((pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L hL

/-- Descending the original auxiliary frame preserves the already selected
original numerator and denominator, their full ideals, and finite local freeness.
Every conclusion uses the same new stage and the same transition. -/
theorem exists_original_frame_refinement_of_finitePair
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    (B C D : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
    (b : B ⟶ C) (cB : Cone B) (hcB : IsLimit cB)
    [∀ i, CompactSpace (B.obj i)] [∀ i, QuasiSeparatedSpace (B.obj i)]
    (c : Cone C) (bLim : cB.pt ⟶ c.pt)
    (hb : ∀ i, cB.π.app i ≫ b.app i = bLim ≫ c.π.app i)
    (q : C ⟶ D)
    (hcart : ∀ {i j} (f : j ⟶ i), IsPullback (C.map f) (q.app j) (q.app i) (D.map f))
    (i : I) (F : Bool → (C.obj i).Modules) [∀ z, (F z).IsFinitePresentation]
    [∀ z, SheafOfModules.IsInvertible (C.obj i).sheaf.obj
      (C.obj i).ringCatSheaf.property (F z)]
    (M : Bool → c.pt.Modules)
    [∀ z, SheafOfModules.IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property (M z)]
    (E : ∀ z, M z ≅ (pullback (c.π.app i)).obj (F z))
    (sOriginal : ∀ z, Γ(M z, ⊤)) (s : ∀ z, Γ(F z, ⊤))
    (hrec : ∀ z, Hom.app (E z).hom ⊤ (sOriginal z) =
      pullbackGlobalSections (c.π.app i) (F z) (s z))
    (hfin : ∀ z, Stacks.Morphisms.IsFiniteLocallyFree
      ((zeroScheme (C.obj i) (F z) (s z)).subschemeι ≫ q.app i))
    (eOriginal : (pullback bLim).obj (M false) ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    (hOne : Hom.app eOriginal.hom ⊤
      (pullbackGlobalSections bLim (M false) (sOriginal false)) = (1 : Γ(cB.pt, ⊤))) :
    let eLim := (pullback bLim).mapIso (E false).symm ≪≫ eOriginal
    ∃ (j : I) (f : j ⟶ i)
      (e : (pullback (b.app j)).obj ((pullback (C.map f)).obj (F false)) ≅
        SheafOfModules.unit (B.obj j).ringCatSheaf),
      ((pullback (cB.π.app j)).map
          ((pullbackSquareIso (B.map f) (b.app i) (b.app j) (C.map f)
            (b.naturality f) (F false)).hom ≫ e.hom) ≫ (pullbackUnitIso (cB.π.app j)).hom =
        canHom (cB.π.app j) (B.map f) (cB.π.app i) (cB.w f)
          ((pullback (b.app i)).obj (F false)) ≫
          (pullbackSquareIso (cB.π.app i) (b.app i) bLim (c.π.app i) (hb i) (F false)).hom ≫
          eLim.hom) ∧
      Hom.app e.hom ⊤
        (pullbackGlobalSections (b.app j) ((pullback (C.map f)).obj (F false))
          (pullbackGlobalSections (C.map f) (F false) (s false))) = (1 : Γ(B.obj j, ⊤)) ∧
      ∀ z, Hom.app
          (refinedSectionModelIso (c.π.app j) (C.map f) (c.π.app i) (c.w f) (F z) (E z)).hom ⊤
          (sOriginal z) =
        pullbackGlobalSections (c.π.app j) ((pullback (C.map f)).obj (F z))
          (pullbackGlobalSections (C.map f) (F z) (s z)) ∧
        Stacks.Morphisms.IsFiniteLocallyFree
          ((zeroScheme (C.obj j) ((pullback (C.map f)).obj (F z))
            (pullbackGlobalSections (C.map f) (F z) (s z))).subschemeι ≫ q.app j) ∧
        (zeroScheme (C.obj j) ((pullback (C.map f)).obj (F z))
          (pullbackGlobalSections (C.map f) (F z) (s z))).comap (c.π.app j) =
            zeroScheme c.pt (M z) (sOriginal z) := by
  dsimp only
  obtain ⟨j, f, e, he, hOne'⟩ := exists_original_boundaryFrame_modeledSections_one_of_isLimit
    B C b cB hcB c bLim hb i (F false) (M false) (E false) eOriginal
    (fun _ : PUnit.{1} => sOriginal false) (fun _ : PUnit.{1} => s false)
    (fun _ => hrec false) (fun _ => hOne)
  refine ⟨j, f, e, he, hOne' PUnit.unit, fun z => ⟨?_, ?_, ?_⟩⟩
  · exact refinedSectionModelIso_pullback_recovery
      (c.π.app j) (C.map f) (c.π.app i) (c.w f) (F z) (E z) _ _ (hrec z)
  · apply (zeroScheme_cartesian_isFiniteLocallyFree_iff
      (C.map f) (q.app j) (q.app i) (D.map f) (hcart f) (F z) (s z)).mpr
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Stacks.Morphisms.IsFiniteLocallyFree)
      (IsPullback.of_hasPullback (D.map f)
        ((zeroScheme (C.obj i) (F z) (s z)).subschemeι ≫ q.app i)).flip (hfin z)
  · refine (congrArg (fun J : (C.obj j).IdealSheafData => J.comap (c.π.app j))
      (Stacks.Divisors.zeroScheme_pullback (C.map f) (F z) (s z))).trans ?_
    rw [← Scheme.IdealSheafData.comap_comp, c.w f]
    exact (Stacks.Divisors.zeroScheme_pullback (c.π.app i) (F z) (s z)).symm.trans
      (zeroScheme_eq_of_iso (E z) (hrec z)).symm

end AlgebraicGeometry.Scheme.Modules
