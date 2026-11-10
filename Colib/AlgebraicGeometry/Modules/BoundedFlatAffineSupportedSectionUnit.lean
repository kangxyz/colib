/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSupportedSectionReindex
public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSectionUnitNaturality

/-!
# The unchanged Laurent-unit action on actual supported sections

The original section-unit automorphism restricts through the fully faithful support inclusion.
Both its forward and inverse components remain the original section maps, and coefficient
naturality retains the whole specified open-pair square. Original evaluation therefore sees
the same geometric scalar action. This supplies the unit compatibility required by a supported
Bass seed; Waldhausen and seed constructions remain separate.

Adapted from Quillen `SupportedSectionUnit.lean:33-72` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}

attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineEvaluationAt
  boundedAboveFlatPerfectGlobalUnitIso

/-- Restrict the original global-unit automorphism to the actual supported section category. -/
def boundedAboveFlatAffineSupportedSectionUnitIso (j : U ⟶ Spec R) [IsOpenImmersion j]
    (r : (Γ(Spec R, ⊤))ˣ) :
    𝟭 (BoundedAboveFlatAffineSupportedSections j) ≅ 𝟭 (BoundedAboveFlatAffineSupportedSections j) :=
  Functor.IdentityAutomorphism.lift (boundedAboveFlatAffineSectionSupported j).ι
    (boundedAboveFlatAffineSectionUnitIso R r)

/-- Forgetting support retains the actual original forward scalar map. -/
theorem boundedAboveFlatAffineSupportedSectionUnitIso_hom (j : U ⟶ Spec R) [IsOpenImmersion j]
    (r : (Γ(Spec R, ⊤))ˣ) (s : BoundedAboveFlatAffineSupportedSections j) :
    ((boundedAboveFlatAffineSupportedSectionUnitIso j r).hom.app s).hom =
      (boundedAboveFlatAffineSectionUnitIso R r).hom.app s.obj :=
  Functor.IdentityAutomorphism.map_lift_hom (boundedAboveFlatAffineSectionSupported j).ι
    (boundedAboveFlatAffineSectionUnitIso R r) s

/-- Forgetting support also retains the original inverse scalar map. -/
theorem boundedAboveFlatAffineSupportedSectionUnitIso_inv (j : U ⟶ Spec R) [IsOpenImmersion j]
    (r : (Γ(Spec R, ⊤))ˣ) (s : BoundedAboveFlatAffineSupportedSections j) :
    ((boundedAboveFlatAffineSupportedSectionUnitIso j r).inv.app s).hom =
      (boundedAboveFlatAffineSectionUnitIso R r).inv.app s.obj :=
  Functor.IdentityAutomorphism.map_lift_inv (boundedAboveFlatAffineSectionSupported j).ι
    (boundedAboveFlatAffineSectionUnitIso R r) s

/-- The unchanged unit commutes strictly with the original supported coefficient restriction. -/
theorem boundedAboveFlatAffineSupportedSectionUnitIso_coefficient_hom
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)
    (r : (Γ(Spec R, ⊤))ˣ) :
    Functor.whiskerRight (boundedAboveFlatAffineSupportedSectionUnitIso j r).hom
        (boundedAboveFlatAffineSupportedSectionsMap j j' f l h) =
      Functor.whiskerLeft (boundedAboveFlatAffineSupportedSectionsMap j j' f l h)
        (boundedAboveFlatAffineSupportedSectionUnitIso j'
          (Units.map (Spec.map f).appTop.hom.toMonoidHom r)).hom := by
  apply NatTrans.ext
  funext s
  simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app]
  apply ObjectProperty.hom_ext
  change (boundedAboveFlatAffineSectionsMap f).map
    ((boundedAboveFlatAffineSupportedSectionUnitIso j r).hom.app s).hom = _
  rw [boundedAboveFlatAffineSupportedSectionUnitIso_hom,
    boundedAboveFlatAffineSupportedSectionUnitIso_hom]
  exact NatTrans.congr_app (boundedAboveFlatAffineSectionUnitIso_coefficient_hom f r) s.obj


end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    SupportedSectionUnit.lean:33-72"
  "adaptation" "Actual supported unit and whole coefficient-square naturality"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionUnitIso
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionUnitIso_hom
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionUnitIso_inv
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionUnitIso_coefficient_hom
