/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.SourceChangedMatching
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.BoundarySupport
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeUnits

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
  let p := parameterMap (f ≫ bS) j
  let g := parameterMap bS f
  apply pullback.hom_ext
  · have h : (p ≫ g) ≫ projection bS = projection (j ≫ f ≫ bS) ≫ j ≫ f :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun m => p ≫ m) (parameterMap_projection bS f)).trans
          (parameterMap_projection_assoc (f ≫ bS) j f))
    exact h.trans (parameterMap_projection bS (j ≫ f)).symm
  · let k := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
    have h : (p ≫ g) ≫ pullback.snd bS k = pullback.snd (j ≫ f ≫ bS) k :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun m => p ≫ m) (parameterMap_snd bS f)).trans
          (parameterMap_snd (f ≫ bS) j))
    exact h.trans (parameterMap_snd bS (j ≫ f)).symm

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
  let M := (Modules.pullback (projection b)).obj L
  let p := parameterMap b j
  let e := parameterSectionRestrictionIso b j L
  let s := familySection (j ≫ b) ((Modules.pullback j).obj L)
    (pullbackGlobalSections j L a) (pullbackGlobalSections j L c)
  have h₁ := zeroScheme_pullback p M (familySection b L a c)
  have h₂ := parameterSectionRestrictionIso_familySection b j L a c
  have h₃ := zeroScheme_congr_iso e s
  exact h₁.symm.trans ((congrArg (fun t => zeroScheme (parameterSpace (j ≫ b))
    ((Modules.pullback p).obj M) t) h₂.symm).trans h₃)

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
    (he : e.app ⊤ (pullbackGlobalSections i L a) = (1 : Γ(Z, ⊤))) :
    IsFinite (familySource bS (j ≫ f) ((Modules.pullback j).obj L)
        (pullbackGlobalSections j L a) (pullbackGlobalSections j L c)) ∧
      Flat (familySource bS (j ≫ f) ((Modules.pullback j).obj L)
        (pullbackGlobalSections j L a) (pullbackGlobalSections j L c)) := by
  obtain ⟨hfin, hcart⟩ := finite_relativeCartier_family_on_open_of_boundary_frame
    i L a c bS f j hcover h e he
  rw [familyZero_comap_parameterMap, parameterMap_comp] at hfin hcart
  exact ⟨hfin, hcart.2⟩

end AlgebraicGeometry.Scheme.PolynomialSectionPencil
