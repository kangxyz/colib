/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.FiniteSectionPairs

/-! # Finite local freeness by refining the same already descended sections

The original full zero schemes are identified by their actual section models.
One refinement makes all literal pulled-back stage zero schemes finite locally
free, without selecting replacement sections or changing their full ideals.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Morphisms
open Stacks.AlgebraicGeometry.ModuleLimits
universe u v w
namespace AlgebraicGeometry

local instance instModeledZeroSchemeRefinementInvertiblePullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L hL

/-- Refine an already fixed finite family of section models until their entire
zero schemes are finite locally free. All original full ideals are recovered. -/
theorem exists_modeledZeroSchemes_finiteLocallyFree_refinement
    {I : Type u} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D C : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, IsNoetherian (D.obj i)] [∀ i, IsNoetherian (C.obj i)]
    (d : Cone D) (hd : IsLimit d) (c : Cone C)
    (q : C ⟶ D) [∀ i, LocallyOfFiniteType (q.app i)] (qLimit : c.pt ⟶ d.pt)
    (hLimit : ∀ i, IsPullback (c.π.app i) qLimit (q.app i) (d.π.app i))
    (hcart : ∀ {i j} (f : j ⟶ i), IsPullback (C.map f) (q.app j) (q.app i) (D.map f))
    (i : I) {κ : Type w} [Finite κ] (L : κ → (C.obj i).Modules)
    [∀ a, SheafOfModules.IsInvertible
      (C.obj i).sheaf.obj (C.obj i).ringCatSheaf.property (L a)]
    (M : κ → c.pt.Modules)
    [∀ a, SheafOfModules.IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property (M a)]
    (E : ∀ a, M a ≅ (Scheme.Modules.pullback (c.π.app i)).obj (L a))
    (s : ∀ a, Γ(M a, ⊤)) (t : ∀ a, Γ(L a, ⊤))
    (ht : ∀ a, Scheme.Modules.Hom.app (E a).hom ⊤ (s a) =
      pullbackGlobalSections (c.π.app i) (L a) (t a))
    (hs : ∀ a, IsFiniteLocallyFree ((zeroScheme c.pt (M a) (s a)).subschemeι ≫ qLimit)) :
    ∃ (j : I) (f : j ⟶ i), ∀ a,
      IsFiniteLocallyFree
        ((zeroScheme (C.obj j) ((Scheme.Modules.pullback (C.map f)).obj (L a))
          (pullbackGlobalSections (C.map f) (L a) (t a))).subschemeι ≫ q.app j) ∧
      (zeroScheme (C.obj j) ((Scheme.Modules.pullback (C.map f)).obj (L a))
        (pullbackGlobalSections (C.map f) (L a) (t a))).comap (c.π.app j) =
          zeroScheme c.pt (M a) (s a) := by
  have hz a : zeroScheme c.pt ((Scheme.Modules.pullback (c.π.app i)).obj (L a))
      (pullbackGlobalSections (c.π.app i) (L a) (t a)) = zeroScheme c.pt (M a) (s a) :=
    (zeroScheme_eq_of_iso (E a) (ht a)).symm
  have hlimit a : IsFiniteLocallyFree
      ((Stacks.Divisors.zeroScheme (pullback (d.π.app i) (q.app i))
        ((Scheme.Modules.pullback (pullback.snd (d.π.app i) (q.app i))).obj (L a))
        (pullbackGlobalSections (pullback.snd (d.π.app i) (q.app i)) (L a) (t a))).subschemeι ≫
          pullback.fst (d.π.app i) (q.app i)) := by
    apply (zeroSchemeBaseChange_finiteLocallyFree_iff (d.π.app i) (q.app i) (L a) (t a)).mpr
    apply (zeroScheme_cartesian_isFiniteLocallyFree_iff
      (c.π.app i) qLimit (q.app i) (d.π.app i) (hLimit i) (L a) (t a)).mp
    change IsFiniteLocallyFree
      ((zeroScheme c.pt ((Scheme.Modules.pullback (c.π.app i)).obj (L a))
        (pullbackGlobalSections (c.π.app i) (L a) (t a))).subschemeι ≫ qLimit)
    rw [hz a]
    exact hs a
  obtain ⟨j, f, hf⟩ := exists_zeroSchemes_isFiniteLocallyFree_of_isLimit_finite
    D d hd i (q.app i) L t hlimit
  refine ⟨j, f, fun a => ⟨?_, ?_⟩⟩
  · exact (zeroScheme_cartesian_isFiniteLocallyFree_iff
      (C.map f) (q.app j) (q.app i) (D.map f) (hcart f) (L a) (t a)).mpr
      ((zeroSchemeBaseChange_finiteLocallyFree_iff (D.map f) (q.app i) (L a) (t a)).mp (hf a))
  · refine (congrArg (fun J : (C.obj j).IdealSheafData => J.comap (c.π.app j))
      (Stacks.Divisors.zeroScheme_pullback (C.map f) (L a) (t a))).trans ?_
    rw [← Scheme.IdealSheafData.comap_comp, c.w f]
    exact (Stacks.Divisors.zeroScheme_pullback (c.π.app i) (L a) (t a)).symm.trans (hz a)

end AlgebraicGeometry
