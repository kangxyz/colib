/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.SupportedDerivedVanishing
public import Colib.AlgebraicGeometry.Modules.SupportedUnionGeometry
public import Colib.AlgebraicGeometry.Modules.PerfectQcqsComplement

/-!
# Supported stabilized perfect extensions on qcqs schemes

Extension by zero gives a perfect complex on the union neighborhood. The ordinary
extension theorem is applied to its sum with its shift. Both summands vanish on the
prescribed open, so the global perfect extension is supported. Stabilization is essential.
-/

attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-- The actual derived restriction comparison carries a stabilized isomorphism to the
stabilized isomorphism of the actual restricted complexes. -/
def restrictDerivedBiprodShiftIso {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {A B : CochainComplex X.Modules ℤ}
    (e : DerivedCategory.Q.obj A ≅
      DerivedCategory.Q.obj B ⊞ (DerivedCategory.Q.obj B)⟦(1 : ℤ)⟧) :
    DerivedCategory.Q.obj (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj A) ≅
      DerivedCategory.Q.obj (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj B) ⊞
        (DerivedCategory.Q.obj
          (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj B))⟦(1 : ℤ)⟧ :=
  ((restrictFunctor j).mapDerivedCategoryFactors.app A).symm ≪≫
    (restrictFunctor j).mapDerivedCategory.mapIso e ≪≫
    (restrictFunctor j).mapDerivedCategory.mapBiprod _ _ ≪≫
    biprod.mapIso ((restrictFunctor j).mapDerivedCategoryFactors.app B)
      (((restrictFunctor j).mapDerivedCategory.commShiftIso 1).app (DerivedCategory.Q.obj B) ≪≫
        (shiftFunctor _ (1 : ℤ)).mapIso ((restrictFunctor j).mapDerivedCategoryFactors.app B))

variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

omit [CompactSpace U] in
/-- A supported local perfect complex, summed with its shift, extends to a supported
perfect complex when the union neighborhood is compact. -/
theorem exists_perfectSupported_restrict_iso_biprod_shift_of_union_compact
    (hW : IsCompact ((j.opensRange ⊔ T : X.Opens) : Set X))
    (E : CochainComplex U.Modules ℤ) (hE : perfectSupported (j ⁻¹ᵁ T).ι E) :
    ∃ R : CochainComplex X.Modules ℤ, perfectSupported T.ι R ∧
      Nonempty (DerivedCategory.Q.obj
          (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj R) ≅
        DerivedCategory.Q.obj E ⊞ (DerivedCategory.Q.obj E)⟦(1 : ℤ)⟧) := by
  let W := j.opensRange ⊔ T
  let i := W.ι
  let k := supportedUnionLift j T
  let F := (Complex.extensionByZero k).obj E
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW
  have hE' : perfectSupported (k ⁻¹ᵁ (i ⁻¹ᵁ T)).ι E := by
    have hik : k ≫ i = j := supportedUnionLift_ι j T
    rw [← Scheme.Hom.comp_preimage, hik]
    exact hE
  have hF : perfectSupported (i ⁻¹ᵁ T).ι F :=
    perfectSupported_extensionByZero_of_cover k (i ⁻¹ᵁ T)
      (supportedUnionLift_cover j T) hE'
  obtain ⟨R, hR, ⟨eR⟩⟩ := exists_isPerfectComplex_restrict_iso_biprod_shift i F hF.1
  have hRT : (((restrictFunctor T.ι).mapHomologicalComplex (.up ℤ)).obj R).Acyclic := by
    apply (restrictAcyclic_preimage_iff_of_le T W le_sup_right R).1
    rw [acyclic_iff_isZero_derived]
    let eT := restrictDerivedBiprodShiftIso (i ⁻¹ᵁ T).ι eR
    apply eT.isZero_iff.2
    have hz := (acyclic_iff_isZero_derived _).1 hF.2
    exact (biprod_isZero_iff _ _).2 ⟨hz, (shiftFunctor _ (1 : ℤ)).map_isZero hz⟩
  let eU := restrictDerivedBiprodShiftIso k eR
  let eE := DerivedCategory.Q.mapIso ((Complex.extensionByZeroRestrictIso k).app E)
  exact ⟨R, ⟨hR, hRT⟩, ⟨(DerivedCategory.Q.mapIso
    ((supportedUnionRestrictIso j T).app R)).symm ≪≫ eU ≪≫
      biprod.mapIso eE ((shiftFunctor _ (1 : ℤ)).mapIso eE)⟩⟩

/-- Compactness of the vanishing open suffices for the supported stabilized extension. -/
@[colib_tag "COL-0333"]
theorem exists_perfectSupported_restrict_iso_biprod_shift_of_qcqs
    (hT : IsCompact (T : Set X))
    (E : CochainComplex U.Modules ℤ) (hE : perfectSupported (j ⁻¹ᵁ T).ι E) :
    ∃ R : CochainComplex X.Modules ℤ, perfectSupported T.ι R ∧
      Nonempty (DerivedCategory.Q.obj
          (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj R) ≅
        DerivedCategory.Q.obj E ⊞ (DerivedCategory.Q.obj E)⟦(1 : ℤ)⟧) :=
  exists_perfectSupported_restrict_iso_biprod_shift_of_union_compact j T
    (isCompact_supportedUnion j T hT) E hE

end AlgebraicGeometry.Scheme.Modules
