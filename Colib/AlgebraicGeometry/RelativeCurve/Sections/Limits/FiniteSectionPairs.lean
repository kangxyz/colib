/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.CanonicalSections
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.ZeroSchemeCartesian

/-! # Actual finite families of sections with finite locally free whole zero schemes

First descend the original section values, then refine their common stage using
the finite-presentation descent of the full zero schemes. All later sections are
literal pullbacks of that same family. The ambient squares are Cartesian; no
assumed section witness or assumed eventual zero-scheme property is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Morphisms
open Stacks.AlgebraicGeometry.ModuleLimits

universe u v w

namespace AlgebraicGeometry

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L hL

/-- Actual sections on a Cartesian limit descend together; at one further stage
their original literal pullbacks have finite locally free whole zero schemes.
The first comparison records exactly the original section, not only its support. -/
@[stacks 06AC "finite locally free whole-morphism descent ingredient after actual section descent",
  colib_tag "COL-1113"]
theorem exists_sections_and_finiteLocallyFree_zeroSchemes_of_isLimit
    {I : Type u} [Category.{v} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D C : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (C.map f)]
    [∀ i, IsNoetherian (D.obj i)] [∀ i, IsNoetherian (C.obj i)]
    (d : Cone D) (hd : IsLimit d) (c : Cone C) (hc : IsLimit c)
    (q : C ⟶ D) [∀ i, LocallyOfFiniteType (q.app i)] (qLimit : c.pt ⟶ d.pt)
    (hLimit : ∀ i, IsPullback (c.π.app i) qLimit (q.app i) (d.π.app i))
    (hcart : ∀ {i j} (f : j ⟶ i), IsPullback (C.map f) (q.app j) (q.app i) (D.map f))
    (i : I) {κ : Type w} [Finite κ] (L : κ → (C.obj i).Modules)
    [∀ a, (L a).IsFinitePresentation]
    [∀ a, SheafOfModules.IsInvertible
      (C.obj i).sheaf.obj (C.obj i).ringCatSheaf.property (L a)]
    (s : ∀ a, Γ((Scheme.Modules.pullback (c.π.app i)).obj (L a), ⊤))
    (hs : ∀ a, IsFiniteLocallyFree
      ((zeroScheme c.pt ((Scheme.Modules.pullback (c.π.app i)).obj (L a)) (s a)).subschemeι ≫
        qLimit)) :
    ∃ (j : I) (e : j ⟶ i)
      (t : ∀ a, Γ((Scheme.Modules.pullback (C.map e)).obj (L a), ⊤))
      (k : I) (f : k ⟶ j),
      (∀ a, Scheme.Modules.Hom.app
        (canHom (c.π.app j) (C.map e) (c.π.app i) (c.w e) (L a)) ⊤
        (pullbackGlobalSections (c.π.app j)
          ((Scheme.Modules.pullback (C.map e)).obj (L a)) (t a)) = s a) ∧
      ∀ a, IsFiniteLocallyFree
        ((zeroScheme (C.obj k)
          ((Scheme.Modules.pullback (C.map f)).obj
            ((Scheme.Modules.pullback (C.map e)).obj (L a)))
          (pullbackGlobalSections (C.map f)
            ((Scheme.Modules.pullback (C.map e)).obj (L a)) (t a))).subschemeι ≫ q.app k) ∧
        (zeroScheme (C.obj k)
          ((Scheme.Modules.pullback (C.map f)).obj
            ((Scheme.Modules.pullback (C.map e)).obj (L a)))
          (pullbackGlobalSections (C.map f)
            ((Scheme.Modules.pullback (C.map e)).obj (L a)) (t a))).comap (c.π.app k) =
          zeroScheme c.pt ((Scheme.Modules.pullback (c.π.app i)).obj (L a)) (s a) := by
  obtain ⟨j, e, t, ht⟩ :=
    exists_globalSections_zeroSchemes_canonical_of_isLimit_finite C c hc i L s
  let M a := (Scheme.Modules.pullback (C.map e)).obj (L a)
  have hlimit (a : κ) : IsFiniteLocallyFree
      ((Stacks.Divisors.zeroScheme (pullback (d.π.app j) (q.app j))
        ((Scheme.Modules.pullback (pullback.snd (d.π.app j) (q.app j))).obj (M a))
        (pullbackGlobalSections (pullback.snd (d.π.app j) (q.app j)) (M a) (t a))).subschemeι ≫
          pullback.fst (d.π.app j) (q.app j)) := by
    apply (zeroSchemeBaseChange_finiteLocallyFree_iff (d.π.app j) (q.app j) (M a) (t a)).mpr
    apply (zeroScheme_cartesian_isFiniteLocallyFree_iff
      (c.π.app j) qLimit (q.app j) (d.π.app j) (hLimit j) (M a) (t a)).mp
    change IsFiniteLocallyFree
      ((zeroScheme c.pt ((Scheme.Modules.pullback (c.π.app j)).obj (M a))
        (pullbackGlobalSections (c.π.app j) (M a) (t a))).subschemeι ≫ qLimit)
    rw [(ht a).2]
    exact hs a
  obtain ⟨k, f, hf⟩ := exists_zeroSchemes_isFiniteLocallyFree_of_isLimit_finite
    D d hd j (q.app j) M t hlimit
  refine ⟨j, e, t, k, f, fun a => (ht a).1, fun a => ?_⟩
  constructor
  · exact (zeroScheme_cartesian_isFiniteLocallyFree_iff
      (C.map f) (q.app k) (q.app j) (D.map f) (hcart f) (M a) (t a)).mpr
      ((zeroSchemeBaseChange_finiteLocallyFree_iff (D.map f) (q.app j) (M a) (t a)).mp (hf a))
  · refine (congrArg (fun J : (C.obj k).IdealSheafData => J.comap (c.π.app k))
      (Stacks.Divisors.zeroScheme_pullback (C.map f) (M a) (t a))).trans ?_
    rw [← Scheme.IdealSheafData.comap_comp, c.w f]
    exact (Stacks.Divisors.zeroScheme_pullback (c.π.app j) (M a) (t a)).symm.trans (ht a).2

end AlgebraicGeometry
