/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeGraphDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeNonvanishingLocus
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Trivialize
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic

/-!
# The actual canonical frame on an entire disjoint boundary

A section with empty zero scheme gives a specific isomorphism to the structure
sheaf: the inverse of multiplication by that section. Its value on the section is
literally one. Pulling the canonical divisor section to a boundary disjoint from
the entire divisor supplies this frame, without a trivialization premise.

The final application is the actual relative graph and a boundary whose target
coordinate misses the graph target. The whole boundary, including its nilpotents,
is retained. This is the infinity-boundary component of the original
`Modules/Invertible/Frames/RelativeCurve/FullBoundaryFrames.lean`; the marked
component can intersect the graph and requires the separate coordinate frame.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Ample Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {X Z : Scheme.{u}}

/-- Multiplication by a global section, at the actual sheaf-module spelling. -/
def sectionUnitHom (L : X.Modules) (s : Γ(L, ⊤)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ L :=
  L.unitHomEquiv.symm ((Stacks.NonvanishingSpelling.sectionsEquiv X L).symm s)

@[simp]
theorem sectionUnitHom_app_one (L : X.Modules) (s : Γ(L, ⊤)) :
    (sectionUnitHom L s).app ⊤ 1 = s := by
  rw [show (sectionUnitHom L s).app ⊤ 1 =
    (1 : Γ(X, ⊤)) • L.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op s from
    Stacks.NonvanishingSpelling.unitHom_app X L s ⊤ 1]
  simp

/-- Empty scheme-theoretic zeros make multiplication by the section invertible
on the entire scheme, not just on a chosen dense open. -/
theorem isIso_sectionUnitHom_of_zeroScheme_eq_top (L : X.Modules)
    [IsInvertibleModule X L] (s : Γ(L, ⊤)) (hs : zeroScheme X L s = ⊤) :
    IsIso (sectionUnitHom L s) := by
  apply Stacks.SheafOfModules.isIso_of_isIso_val_app
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (fun a : Γ(X, U.unop) =>
    (sectionUnitHom L s).app U.unop a)
  simp_rw [show ∀ a : Γ(X, U.unop), (sectionUnitHom L s).app U.unop a =
    a • L.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op s from
    fun a => Stacks.NonvanishingSpelling.unitHom_app X L s U.unop a]
  apply Stacks.NonvanishingSpelling.bijective_smul X L s
  intro x _
  apply (mem_nonvanishingLocus_iff_notMem_supportSet_zeroScheme L s x).2
  rw [hs]
  exact Set.notMem_empty x

/-- The canonical whole-scheme frame determined by a nowhere-zero section. -/
def frameOfZeroSchemeTop (L : X.Modules) [IsInvertibleModule X L]
    (s : Γ(L, ⊤)) (hs : zeroScheme X L s = ⊤) :
    L ≅ SheafOfModules.unit X.ringCatSheaf :=
  letI := isIso_sectionUnitHom_of_zeroScheme_eq_top L s hs
  (asIso (sectionUnitHom L s)).symm

@[simp]
theorem frameOfZeroSchemeTop_section (L : X.Modules) [IsInvertibleModule X L]
    (s : Γ(L, ⊤)) (hs : zeroScheme X L s = ⊤) :
    (frameOfZeroSchemeTop L s hs).hom.app ⊤ s = 1 := by
  letI := isIso_sectionUnitHom_of_zeroScheme_eq_top L s hs
  have h := congrArg (fun m => m.app ⊤ (1 : Γ(X, ⊤)))
    (IsIso.hom_inv_id (sectionUnitHom L s))
  simpa only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    CategoryTheory.comp_apply, CategoryTheory.id_apply, sectionUnitHom_app_one] using h

/-- A map disjoint from the whole divisor has unit inverse-image ideal. -/
theorem divisor_comap_eq_top_of_disjoint (D : X.IdealSheafData) (i : Z ⟶ X)
    (h : Disjoint (Set.range i) (D.support : Set X)) : D.comap i = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).1
  rw [Scheme.IdealSheafData.support_comap]
  apply TopologicalSpace.Closeds.ext
  apply Set.eq_empty_iff_forall_notMem.2
  intro z hz
  exact Set.disjoint_left.1 h ⟨z, rfl⟩ hz

/-- The pulled-back canonical section has no zeros anywhere on the boundary. -/
theorem canonicalSection_zeroScheme_on_disjoint_boundary
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D] (i : Z ⟶ X)
    (h : Disjoint (Set.range i) (D.support : Set X)) :
    zeroScheme Z ((Modules.pullback i).obj (divisorSheaf D))
      (pullbackGlobalSections i (divisorSheaf D) (divisorSheafGlobalSection D)) = ⊤ := by
  rw [Stacks.Divisors.zeroScheme_pullback, zeroScheme_canonicalSection]
  exact divisor_comap_eq_top_of_disjoint D i h

/-- The actual frame of the graph line on a whole disjoint boundary. It is
constructed from the canonical section and contains no supplied frame. -/
def canonicalDisjointBoundaryFrame (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (i : Z ⟶ X)
    (h : Disjoint (Set.range i) (D.support : Set X)) :
    (Modules.pullback i).obj (divisorSheaf D) ≅ SheafOfModules.unit Z.ringCatSheaf :=
  frameOfZeroSchemeTop _ _ (canonicalSection_zeroScheme_on_disjoint_boundary D i h)

@[simp]
theorem canonicalDisjointBoundaryFrame_coordinate (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] (i : Z ⟶ X)
    (h : Disjoint (Set.range i) (D.support : Set X)) :
    (canonicalDisjointBoundaryFrame D i h).hom.app ⊤
      (pullbackGlobalSections i (divisorSheaf D) (divisorSheafGlobalSection D)) = 1 :=
  frameOfZeroSchemeTop_section _ _ _

variable {S V : Scheme.{u}} (q : X ⟶ S) (r : V ⟶ S)
  (φ : X ⟶ V) (hφ : φ ≫ r = q)

/-- Disjointness is checked in the literal target coordinate of the full product. -/
theorem relativeGraph_disjoint_boundary [IsSeparated r]
    (i : Z ⟶ pullback q r)
    (h : Disjoint (Set.range (i ≫ pullback.snd q r)) (Set.range φ)) :
    Disjoint (Set.range i) ((relativeGraphIdeal q r φ hφ).support : Set (pullback q r)) := by
  rw [relativeGraphIdeal, Scheme.Hom.support_ker,
    (IsClosedImmersion.isClosedEmbedding (relativeGraph q r φ hφ)).isClosed_range.closure_eq]
  apply Set.disjoint_left.2
  rintro y ⟨z, rfl⟩ ⟨x, hx⟩
  apply Set.disjoint_left.1 h ⟨z, rfl⟩
  refine ⟨x, ?_⟩
  have h' := congrArg (fun w => (pullback.snd q r) w) hx
  simpa only [← Scheme.Hom.comp_apply, relativeGraph_snd] using h'

/-- The actual relative graph supplies its own infinity-boundary frame. -/
def relativeGraphBoundaryFrame [IsSeparated r] [SmoothOfRelativeDimension 1 r]
    (i : Z ⟶ pullback q r)
    (h : Disjoint (Set.range (i ≫ pullback.snd q r)) (Set.range φ)) :
    (Modules.pullback i).obj (divisorSheaf (relativeGraphIdeal q r φ hφ)) ≅
      SheafOfModules.unit Z.ringCatSheaf :=
  canonicalDisjointBoundaryFrame _ i (relativeGraph_disjoint_boundary q r φ hφ i h)

@[simp]
theorem relativeGraphBoundaryFrame_coordinate [IsSeparated r]
    [SmoothOfRelativeDimension 1 r] (i : Z ⟶ pullback q r)
    (h : Disjoint (Set.range (i ≫ pullback.snd q r)) (Set.range φ)) :
    (relativeGraphBoundaryFrame q r φ hφ i h).hom.app ⊤
      (pullbackGlobalSections i (divisorSheaf (relativeGraphIdeal q r φ hφ))
        (divisorSheafGlobalSection (relativeGraphIdeal q r φ hφ))) = 1 :=
  canonicalDisjointBoundaryFrame_coordinate _ _ _

end AlgebraicGeometry.Scheme.RelativeCurvePencil
