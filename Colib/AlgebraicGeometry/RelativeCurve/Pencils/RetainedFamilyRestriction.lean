/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.SourceChangedMatching
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.BoundarySupport

/-!
# The literal retained pencil is the full inverse image of the compactified pencil

The actual pullback square of parameter projections compares the two native
coefficient modules and preserves the complete polynomial section. Its zero
ideal is therefore exactly the inverse image of the compactified zero ideal.
This transfers the geometric finiteness proof to the literal retained family
used by correspondences, rather than silently identifying different families.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.PolynomialSectionPencil

open RelativeCurvePencil

variable {R : Type u} [CommRing R] {X C : Scheme.{u}} (b : X ⟶ Spec (.of R))
  (j : C ⟶ X)

/-- The actual parameter coordinate is preserved by change of the original scheme. -/
@[simp]
theorem parameterMap_parameter :
    (parameterMap b j).appTop (parameter b) = parameter (j ≫ b) := by
  change (parameterMap b j).appTop
    ((pullback.snd b _).appTop ((Scheme.ΓSpecIso (.of (Polynomial R))).inv Polynomial.X)) = _
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, parameterMap_snd]
  rfl

/-- Polynomial parameter maps preserve composition, with the same source and
second coordinate. -/
@[reassoc]
theorem parameterMap_comp {S : Scheme.{u}} (bS : S ⟶ Spec (.of R))
    (f : X ⟶ S) : parameterMap (f ≫ bS) j ≫ parameterMap bS f =
      parameterMap bS (j ≫ f) := by
  apply pullback.hom_ext
  · change _ ≫ projection bS = _ ≫ projection bS
    simp only [Category.assoc, parameterMap_projection]
  · simp only [Category.assoc, parameterMap_snd]

/-- The literal comparison between the retained coefficient line and the
restriction of the compactified coefficient line. -/
def parameterSectionRestrictionIso (L : X.Modules) :
    (Modules.pullback (projection (j ≫ b))).obj ((Modules.pullback j).obj L) ≅
      (Modules.pullback (parameterMap b j)).obj ((Modules.pullback (projection b)).obj L) :=
  boundaryPullbackSquareIso j (projection b) (projection (j ≫ b)) (parameterMap b j)
    (parameterMap_projection b j).symm L

/-- The comparison preserves the entire actual polynomial section. -/
theorem parameterSectionRestrictionIso_familySection (L : X.Modules) (a c : Γ(L, ⊤)) :
    (parameterSectionRestrictionIso b j L).hom.app ⊤
      (familySection (j ≫ b) ((Modules.pullback j).obj L)
        (pullbackGlobalSections j L a) (pullbackGlobalSections j L c)) =
      pullbackGlobalSections (parameterMap b j) ((Modules.pullback (projection b)).obj L)
        (familySection b L a c) := by
  simp only [familySection, map_add, map_sub, Modules.Hom.app_smul,
    SectionsEqualizer.pullbackGlobalSections_smul, parameterMap_parameter,
    parameterSectionRestrictionIso, boundaryPullbackSquareIso_section]

/-- Equality of the full actual zero ideals, before any reduction or passage to cycles. -/
theorem familyZero_comap_parameterMap (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (a c : Γ(L, ⊤)) :
    (familyZero b L a c).comap (parameterMap b j) =
      familyZero (j ≫ b) ((Modules.pullback j).obj L)
        (pullbackGlobalSections j L a) (pullbackGlobalSections j L c) := by
  change (zeroScheme (parameterSpace b) ((Modules.pullback (projection b)).obj L)
    (familySection b L a c)).comap (parameterMap b j) = _
  rw [← zeroScheme_pullback, ← parameterSectionRestrictionIso_familySection,
    zeroScheme_congr_iso]
  rfl

/-- The finiteness and flatness proved on the compactification belong to the
literal retained familySource used by finite correspondences. -/
theorem finite_flat_retainedFamily_of_boundary_frame {S Z : Scheme.{u}}
    (bS : S ⟶ Spec (.of R)) (f : X ⟶ S) [IsProper f] [IsAffine S]
    [IsOpenImmersion j] [C.IsQuasiAffine] [SmoothOfRelativeDimension 1 (j ≫ f)]
    (i : Z ⟶ X) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (a c : Γ(L, ⊤))
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)
    (h : pullbackGlobalSections i L a = pullbackGlobalSections i L c)
    (e : (Modules.pullback i).obj L ⟶ SheafOfModules.unit Z.ringCatSheaf)
    (he : e.app ⊤ (pullbackGlobalSections i L a) = 1) :
    IsFinite (familySource bS (j ≫ f) ((Modules.pullback j).obj L)
        (pullbackGlobalSections j L a) (pullbackGlobalSections j L c)) ∧
      Flat (familySource bS (j ≫ f) ((Modules.pullback j).obj L)
        (pullbackGlobalSections j L a) (pullbackGlobalSections j L c)) := by
  obtain ⟨hfin, hcart⟩ := finite_relativeCartier_family_on_open_of_boundary_frame
    i L a c bS f j hcover h e he
  rw [familyZero_comap_parameterMap, parameterMap_comp] at hfin hcart
  exact ⟨hfin, hcart.2⟩

end AlgebraicGeometry.Scheme.PolynomialSectionPencil
