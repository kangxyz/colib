/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.AuxiliaryFinitePair
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.FinitePairFrameRefinement

/-! # One original auxiliary finite pair and its original boundary frame

Descend the original auxiliary module and both original sections first, then
refine that same pair to descend the specified original auxiliary frame. Both
full zero schemes remain finite locally free and retain their original limit ideals.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
namespace AlgebraicGeometry.Scheme.Modules
local instance framedPairStacksInvertible {X : Scheme.{u}} (M : X.Modules)
    [hM : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M :=
  Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hM

local instance framedPairPullbackInvertible {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [hM : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property ((pullback f).obj M) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom M hM

local instance framedPairModulesInvertible {X : Scheme.{u}} (M N : X.Modules)
    [hM : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    [hN : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] (z : Bool) :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (auxiliaryPairModules M N z) := by
  cases z
  · exact hN
  · exact (Stacks.SheafOfModules.isInvertible_tensorSheaf
      X.sheaf.obj X.ringCatSheaf.property M N).toAlgebraicGeometry

set_option maxHeartbeats 800000 in
-- Retain all original module isomorphisms through the four actual refinement stages.
/-- The original auxiliary module, numerator, denominator and auxiliary frame
are realized by one sequence of refinements, not independent existential choices.
The fixed root model is only pulled back; the original boundary value is one. -/
theorem exists_original_auxiliaryFramedFinitePair_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I] [EssentiallySmall.{u} I]
    (D C B : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (B.map f)]
    [∀ i, CompactSpace (B.obj i)] [∀ i, QuasiSeparatedSpace (B.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (C.map f)]
    [∀ i, IsNoetherian (D.obj i)] [∀ i, IsNoetherian (C.obj i)]
    (d : Cone D) (hd : IsLimit d) (c : Cone C) (hc : IsLimit c)
    (q : C ⟶ D) [∀ i, LocallyOfFiniteType (q.app i)] (qLimit : c.pt ⟶ d.pt)
    (hLimit : ∀ i, IsPullback (c.π.app i) qLimit (q.app i) (d.π.app i))
    (hcart : ∀ {i j} (f : j ⟶ i), IsPullback (C.map f) (q.app j) (q.app i) (D.map f))
    (ι : B ⟶ C) (cB : Cone B) (hcB : IsLimit cB) (bLim : cB.pt ⟶ c.pt)
    (hb : ∀ i, cB.π.app i ≫ ι.app i = bLim ≫ c.π.app i)
    (i : I) (L : (C.obj i).Modules)
    [SheafOfModules.IsInvertible (C.obj i).sheaf.obj (C.obj i).ringCatSheaf.property L]
    (M N : c.pt.Modules)
    [SheafOfModules.IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property M]
    [hN : SheafOfModules.IsInvertible c.pt.sheaf.obj c.pt.ringCatSheaf.property N]
    (eM : M ≅ (pullback (c.π.app i)).obj L)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor c.pt.sheaf).obj M).obj N, ⊤))
    (b : Γ(N, ⊤))
    (hs : ∀ z, Stacks.Morphisms.IsFiniteLocallyFree
      ((zeroScheme c.pt (auxiliaryPairModules M N z) (auxiliaryPairSections M N a b z)).subschemeι ≫
        qLimit))
    (eOriginal : (pullback bLim).obj N ≅ SheafOfModules.unit cB.pt.ringCatSheaf)
    (hOne : Hom.app eOriginal.hom ⊤ (pullbackGlobalSections bLim N b) =
      (1 : Γ(cB.pt, ⊤))) :
    ∃ (j : I) (e : j ⟶ i) (Nj : (C.obj j).Modules)
      (_hNj : SheafOfModules.IsInvertible (C.obj j).sheaf.obj (C.obj j).ringCatSheaf.property Nj)
      (eN : N ≅ (pullback (c.π.app j)).obj Nj),
      let F := auxiliaryPairModules ((pullback (C.map e)).obj L) Nj
      let E := auxiliaryPairModelIsos (c.π.app j) (C.map e) (c.π.app i) (c.w e) L Nj M N eM eN
      ∃ (k : I) (f : k ⟶ j) (t : ∀ z, Γ((pullback (C.map f)).obj (F z), ⊤))
        (l : I) (g : l ⟶ k),
        let G z := (pullback (C.map g)).obj ((pullback (C.map f)).obj (F z))
        let r z := pullbackGlobalSections (C.map g) ((pullback (C.map f)).obj (F z)) (t z)
        let E₁ z := refinedSectionModelIso
          (c.π.app k) (C.map f) (c.π.app j) (c.w f) (F z) (E z)
        let E₂ z := refinedSectionModelIso
          (c.π.app l) (C.map g) (c.π.app k) (c.w g) ((pullback (C.map f)).obj (F z)) (E₁ z)
        let eLim := (pullback bLim).mapIso (E₂ false).symm ≪≫ eOriginal
        ∃ (m : I) (h : m ⟶ l)
          (eAux : (pullback (ι.app m)).obj ((pullback (C.map h)).obj (G false)) ≅
            SheafOfModules.unit (B.obj m).ringCatSheaf),
          ((pullback (cB.π.app m)).map
              ((pullbackSquareIso (B.map h) (ι.app l) (ι.app m) (C.map h)
                (ι.naturality h) (G false)).hom ≫ eAux.hom) ≫
              (pullbackUnitIso (cB.π.app m)).hom =
            canHom (cB.π.app m) (B.map h) (cB.π.app l) (cB.w h)
              ((pullback (ι.app l)).obj (G false)) ≫
              (pullbackSquareIso (cB.π.app l) (ι.app l) bLim (c.π.app l) (hb l) (G false)).hom ≫
              eLim.hom) ∧
          Hom.app eAux.hom ⊤
            (pullbackGlobalSections (ι.app m) ((pullback (C.map h)).obj (G false))
              (pullbackGlobalSections (C.map h) (G false) (r false))) = (1 : Γ(B.obj m, ⊤)) ∧
          ∀ z, Hom.app
              (refinedSectionModelIso (c.π.app m) (C.map h) (c.π.app l) (c.w h) (G z) (E₂ z)).hom ⊤
              (auxiliaryPairSections M N a b z) =
            pullbackGlobalSections (c.π.app m) ((pullback (C.map h)).obj (G z))
              (pullbackGlobalSections (C.map h) (G z) (r z)) ∧
            Stacks.Morphisms.IsFiniteLocallyFree
              ((zeroScheme (C.obj m) ((pullback (C.map h)).obj (G z))
                (pullbackGlobalSections (C.map h) (G z) (r z))).subschemeι ≫ q.app m) ∧
            (zeroScheme (C.obj m) ((pullback (C.map h)).obj (G z))
              (pullbackGlobalSections (C.map h) (G z) (r z))).comap (c.π.app m) =
                zeroScheme c.pt (auxiliaryPairModules M N z) (auxiliaryPairSections M N a b z) := by
  obtain ⟨j, e, Nj, hNj, eN, k, f, t, l, g, hrec, hfin⟩ :=
    exists_original_auxiliaryFinitePair_of_isLimit
      D C d hd c hc q qLimit hLimit hcart i L M N eM a b hs
  let := hNj
  let F := auxiliaryPairModules ((pullback (C.map e)).obj L) Nj
  let E := auxiliaryPairModelIsos (c.π.app j) (C.map e) (c.π.app i) (c.w e) L Nj M N eM eN
  let G z := (pullback (C.map g)).obj ((pullback (C.map f)).obj (F z))
  let r z := pullbackGlobalSections (C.map g) ((pullback (C.map f)).obj (F z)) (t z)
  let E₁ z := refinedSectionModelIso
    (c.π.app k) (C.map f) (c.π.app j) (c.w f) (F z) (E z)
  let E₂ z := refinedSectionModelIso
    (c.π.app l) (C.map g) (c.π.app k) (c.w g) ((pullback (C.map f)).obj (F z)) (E₁ z)
  let (z : Bool) : (G z).IsFinitePresentation :=
    @AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isInvertible (C.obj l) (G z)
      (inferInstanceAs (SheafOfModules.IsInvertible (C.obj l).sheaf.obj
        (C.obj l).ringCatSheaf.property (G z)))
  have H z : Hom.app (E₂ z).hom ⊤ (auxiliaryPairSections M N a b z) =
      pullbackGlobalSections (c.π.app l) (G z) (r z) := by
    apply refinedSectionModelIso_pullback_recovery
    exact refinedSectionModelIso_recovery
      (c.π.app k) (C.map f) (c.π.app j) (c.w f) (F z) (E z) _ _ (hrec z)
  exact ⟨j, e, Nj, hNj, eN, k, f, t, l, g,
    exists_original_frame_refinement_of_finitePair B C D ι cB hcB c bLim hb q hcart l G
      (auxiliaryPairModules M N) E₂ (auxiliaryPairSections M N a b) r H
      (fun z => (hfin z).1) eOriginal hOne⟩

end AlgebraicGeometry.Scheme.Modules
