/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.FiniteZeroSchemes

/-! # Whole zero-scheme finite local freeness in an actual Cartesian square

The closed subscheme pullback is constructed from the actual ideal sheaf and
pasted with the given ambient Cartesian square. This identifies the original
structure maps, including nilpotents, rather than only their supports or cycles.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Morphisms

universe u

namespace AlgebraicGeometry

/-- A whole pulled-back closed subscheme in an actual Cartesian ambient square
has the same finite-local-freeness property as the literal base change of its
original structure map. -/
theorem idealSheaf_comap_isFiniteLocallyFree_iff
    {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (q' : X' ⟶ S')
    (q : X ⟶ S) (b : S' ⟶ S) (h : IsPullback f q' q b)
    (I : X.IdealSheafData) :
    IsFiniteLocallyFree ((I.comap f).subschemeι ≫ q') ↔
      IsFiniteLocallyFree (pullback.fst b (I.subschemeι ≫ q)) := by
  let z := Scheme.IdealSheafData.subschemeMap (I.comap f) I f (I.le_map_comap f)
  have hz : IsPullback z (I.comap f).subschemeι I.subschemeι f := by
    apply IsPullback.flip
    apply isPullback_of_isClosedImmersion
    · exact (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm
    · simp only [Scheme.IdealSheafData.ker_subschemeι]
  have H := (hz.paste_vert h).flip
  have he := H.isoPullback_hom_fst
  have hc := MorphismProperty.cancel_left_of_respectsIso
    (P := @IsFiniteLocallyFree) H.isoPullback.hom
    (pullback.fst b (I.subschemeι ≫ q))
  rw [he] at hc
  exact hc

local instance {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry f.toLRSHom.toShHom L hL

/-- The actual section pullback in a Cartesian square retains the full zero
scheme and the exact finite locally free structure map to the new base. -/
theorem zeroScheme_cartesian_isFiniteLocallyFree_iff
    {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (q' : X' ⟶ S')
    (q : X ⟶ S) (b : S' ⟶ S) (h : IsPullback f q' q b)
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) :
    IsFiniteLocallyFree
      ((Stacks.Divisors.zeroScheme X' ((Scheme.Modules.pullback f).obj L)
        (AlgebraicGeometry.pullbackGlobalSections f L s)).subschemeι ≫ q') ↔
      IsFiniteLocallyFree
        (pullback.fst b ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ q)) := by
  rw [Stacks.Divisors.zeroScheme_pullback]
  exact idealSheaf_comap_isFiniteLocallyFree_iff f q' q b h _

end AlgebraicGeometry
