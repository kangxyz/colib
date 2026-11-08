/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectSupportedQcqsComplement

/-!
# Actual supported complementary complexes

The complement is the actual shift complex. Its support is verified through genuine
homology and derived restriction maps. The stabilized restriction isomorphism is available
in every chosen local derived-category model.
-/

attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-- The actual shift complex retains perfectness and the prescribed support. -/
theorem perfectSupported_shift {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (E : CochainComplex X.Modules ℤ) (hE : perfectSupported j E) (n : ℤ) :
    perfectSupported j (E⟦n⟧) := by
  have hp : RingedSpace.IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj E) :=
    ⟨E, hE.1, ⟨Iso.refl _⟩⟩
  obtain ⟨C, hC, ⟨eC⟩⟩ :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift hp n
  refine ⟨(RingedSpace.isPerfectComplex_iff_of_quasiIsoRoof
    ((CochainComplex.quasiIsoRoof_iff_nonempty_iso C (E⟦n⟧)).2
      ⟨eC ≪≫ ((DerivedCategory.Q.commShiftIso n).app E).symm⟩)).1 hC, ?_⟩
  rw [restrictAcyclic_iff_isZero_derivedRestrict]
  let D := (restrictFunctor j).mapDerivedCategory
  have hz := (restrictAcyclic_iff_isZero_derivedRestrict j E).1 hE.2
  exact ((D.mapIso ((DerivedCategory.Q.commShiftIso n).app E) ≪≫
    (D.commShiftIso n).app (DerivedCategory.Q.obj E)).isZero_iff).2
      ((shiftFunctor _ n).map_isZero hz)

variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

omit [CompactSpace U] in
/-- The supported complement is the actual shift, and the represented direct sum is the
actual biproduct of complexes. This version uses the native small derived model. -/
theorem exists_perfectSupported_restrict_stabilization_small
    (hW : IsCompact ((j.opensRange ⊔ T : X.Opens) : Set X))
    (E : CochainComplex U.Modules ℤ) (hE : perfectSupported (j ⁻¹ᵁ T).ι E) :
    ∃ R : CochainComplex X.Modules ℤ, perfectSupported T.ι R ∧
      perfectSupported (j ⁻¹ᵁ T).ι (E⟦(1 : ℤ)⟧) ∧
      Nonempty (DerivedCategory.Q.obj
          (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj R) ≅
        DerivedCategory.Q.obj (E ⊞ E⟦(1 : ℤ)⟧)) := by
  obtain ⟨R, hR, ⟨eR⟩⟩ :=
    exists_perfectSupported_restrict_iso_biprod_shift_of_union_compact j T hW E hE
  exact ⟨R, hR, perfectSupported_shift (j ⁻¹ᵁ T).ι E hE 1,
    ⟨eR ≪≫ biprod.mapIso (Iso.refl _) ((DerivedCategory.Q.commShiftIso 1).app E).symm ≪≫
      (DerivedCategory.Q.mapBiprod E (E⟦(1 : ℤ)⟧)).symm⟩⟩

section AnyModel

universe d

omit [CompactSpace U] in
/-- A supported perfect complex plus its actual shift extends to a supported global
perfect complex, in any chosen local derived model. Only the union must be compact. -/
@[colib_tag "COL-0333"]
theorem exists_perfectSupported_restrict_stabilization_of_union_compact
    [HasDerivedCategory.{d} U.Modules]
    (hW : IsCompact ((j.opensRange ⊔ T : X.Opens) : Set X))
    (E : CochainComplex U.Modules ℤ) (hE : perfectSupported (j ⁻¹ᵁ T).ι E) :
    ∃ R : CochainComplex X.Modules ℤ, perfectSupported T.ι R ∧
      perfectSupported (j ⁻¹ᵁ T).ι (E⟦(1 : ℤ)⟧) ∧
      Nonempty (DerivedCategory.Q.obj
          (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj R) ≅
        DerivedCategory.Q.obj (E ⊞ E⟦(1 : ℤ)⟧)) := by
  obtain ⟨R, hR, hC, he⟩ := exists_perfectSupported_restrict_stabilization_small j T hW E hE
  refine ⟨R, hR, hC, ?_⟩
  apply (CochainComplex.quasiIsoRoof_iff_nonempty_iso _ _).1
  let := Scheme.Modules.hasDerivedCategory U
  exact (CochainComplex.quasiIsoRoof_iff_nonempty_iso _ _).2 he

/-- Compactness of the vanishing open is a convenient sufficient hypothesis for
supported stabilization in any chosen local derived model. -/
@[colib_tag "COL-0333"]
theorem exists_perfectSupported_restrict_stabilization_of_qcqs
    [HasDerivedCategory.{d} U.Modules] (hT : IsCompact (T : Set X))
    (E : CochainComplex U.Modules ℤ) (hE : perfectSupported (j ⁻¹ᵁ T).ι E) :
    ∃ R : CochainComplex X.Modules ℤ, perfectSupported T.ι R ∧
      perfectSupported (j ⁻¹ᵁ T).ι (E⟦(1 : ℤ)⟧) ∧
      Nonempty (DerivedCategory.Q.obj
          (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj R) ≅
        DerivedCategory.Q.obj (E ⊞ E⟦(1 : ℤ)⟧)) :=
  exists_perfectSupported_restrict_stabilization_of_union_compact j T
    (isCompact_supportedUnion j T hT) E hE

end AnyModel

end AlgebraicGeometry.Scheme.Modules
