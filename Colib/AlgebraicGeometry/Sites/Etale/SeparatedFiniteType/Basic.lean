/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Separated finite-type étale neighborhoods

The full subcategory of actual étale schemes whose structure morphism is separated
and quasi-compact. Étale implies locally finite type, so quasi-compactness supplies
finite type. This is a basis category, not the entire small étale site.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Sites/Etale/SeparatedFiniteType/Nisnevich.lean`
in the motivic source checkpoint of 2026-10-21. Only topology-independent definitions
are retained here; no Nisnevich topology or change-of-base adjunction is imported.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Separated finite-type étale structure morphisms. -/
abbrev etaleSeparatedFiniteType : MorphismProperty Scheme.{u} :=
  (@Etale ⊓ @IsSeparated) ⊓ @QuasiCompact

instance etaleSeparatedFiniteType_isStableUnderBaseChange :
    etaleSeparatedFiniteType.{u}.IsStableUnderBaseChange where
  of_isPullback sq hg :=
    ⟨⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) sq hg.1.1,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsSeparated) sq hg.1.2⟩,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact) sq hg.2⟩

instance etaleSeparatedFiniteType_isMultiplicative :
    etaleSeparatedFiniteType.{u}.IsMultiplicative where
  id_mem X := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  comp_mem f g hf hg := by
    have : Etale f := hf.1.1
    have : Etale g := hg.1.1
    have : IsSeparated f := hf.1.2
    have : IsSeparated g := hg.1.2
    have : QuasiCompact f := hf.2
    have : QuasiCompact g := hg.2
    exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

instance etaleSeparatedFiniteType_hasOfPostcompProperty :
    etaleSeparatedFiniteType.{u}.HasOfPostcompProperty etaleSeparatedFiniteType where
  of_postcomp f g hg hfg := by
    have : Etale g := hg.1.1
    have : IsSeparated g := hg.1.2
    have : Etale (f ≫ g) := hfg.1.1
    have : IsSeparated (f ≫ g) := hfg.1.2
    have : QuasiCompact (f ≫ g) := hfg.2
    exact ⟨⟨Etale.of_comp f g, IsSeparated.of_comp f g⟩, QuasiCompact.of_comp f g⟩

/-- The native small site category, retaining the actual schemes and scheme maps. -/
abbrev EtaleSeparatedFiniteType (S : Scheme.{u}) := etaleSeparatedFiniteType.Over ⊤ S

namespace EtaleSeparatedFiniteType

variable {S T : Scheme.{u}}

instance (X : EtaleSeparatedFiniteType S) : Etale X.hom := X.prop.1.1
instance (X : EtaleSeparatedFiniteType S) : IsSeparated X.hom := X.prop.1.2
instance (X : EtaleSeparatedFiniteType S) : QuasiCompact X.hom := X.prop.2

/-- Forget the structure map, without changing the underlying scheme. -/
abbrev forgetScheme (S : Scheme.{u}) : EtaleSeparatedFiniteType S ⥤ Scheme.{u} :=
  MorphismProperty.Over.forget _ _ S ⋙ Over.forget S

/-- Restrict an ambient smooth presheaf to the finite-type étale neighborhood objects. -/
def toSmoothSite {B : Scheme.{u}} (X : SmoothSite B) :
    EtaleSeparatedFiniteType X.left ⥤ SmoothSite B where
  obj U := SmoothSite.mk (U.hom ≫ X.hom)
  map f := SmoothSite.homMk f.left (by simp [← Category.assoc])
  map_id _ := rfl
  map_comp _ _ := rfl

end EtaleSeparatedFiniteType

end AlgebraicGeometry.Scheme
