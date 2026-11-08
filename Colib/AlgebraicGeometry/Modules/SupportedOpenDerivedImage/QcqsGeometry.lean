/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.SupportedOpenDerivedImage.Complements
public import Colib.AlgebraicGeometry.Modules.SupportedQcqsGeometry

/-!
# Genuine geometric inputs for the supported restriction image

The roof keeps both original global endpoints and constructs an actually supported source.
The complement is the actual shift, so the construction preserves the degree-zero obstruction.
Compactness of the union suffices; compactness of the source open is needed only in the
compact-support-open corollaries. Neither input assumes an equivalence or a density conclusion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

namespace AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  [CompactSpace X] [QuasiSeparatedSpace X] [HasDerivedCategory.{d} U.Modules]

/-- Supported roofs follow from actual union geometry, not an assumed approximation. -/
theorem hasDerivedRoofs_of_union_compact
    (hW : IsCompact ((j.opensRange ⊔ T : X.Opens) : Set X)) : HasDerivedRoofs j T := by
  intro A B hA hB α
  have hp : RingedSpace.IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj B) :=
    ⟨B, hB.1, ⟨Iso.refl _⟩⟩
  have hBqc := isQuasicoherentDerived_of_isPseudoCoherent X _ hp.isPseudoCoherent
  exact exists_perfectSupported_chainMap_roof_of_union_compact j T hW A B hA (fun n =>
    ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((DerivedCategory.homologyFunctorFactors X.Modules n).app B) (hBqc n)) α

/-- The actual shift is a supported complementary complex in every chosen derived model. -/
theorem hasPerfectComplements_of_union_compact
    (hW : IsCompact ((j.opensRange ⊔ T : X.Opens) : Set X)) :
    HasPerfectComplements j T := by
  intro E hE
  obtain ⟨R, hR, hC, he⟩ :=
    exists_perfectSupported_restrict_stabilization_of_union_compact j T hW E hE
  exact ⟨R, E⟦(1 : ℤ)⟧, hR, hC, he⟩

/-- Compact source and compact auxiliary open provide the required compact union. -/
theorem hasDerivedRoofs_of_qcqs [CompactSpace U] (hT : IsCompact (T : Set X)) :
    HasDerivedRoofs j T :=
  hasDerivedRoofs_of_union_compact j T (isCompact_supportedUnion j T hT)

/-- Compact-source, compact-auxiliary-open specialization of actual shift complements. -/
theorem hasPerfectComplements_of_qcqs [CompactSpace U] (hT : IsCompact (T : Set X)) :
    HasPerfectComplements j T :=
  hasPerfectComplements_of_union_compact j T (isCompact_supportedUnion j T hT)

end AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage
