/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectSupportedClosure
public import Colib.AlgebraicGeometry.Modules.PerfectSupportedRestriction
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.OppositeComplexJoint
public import Colib.CategoryTheory.Waldhausen.ComplexFunctor

/-!
# The literal opposite of supported perfect complexes

Native exact-category duality supplies the opposite Waldhausen structure. Its
cofibrations are actual ambient epimorphisms, whose categorical kernels retain
support. Exact restriction preserves this structure on the original chain maps.
No geometric density or compactness is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory HomologicalComplex
open scoped ZeroObject

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

variable {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

local instance : HasFiniteBiproducts (perfectSupported j).FullSubcategory :=
  ExactSubcategory.subcategoryHasFiniteBiproducts (perfectSupported j)

/-- Admissible monomorphisms are exactly the actual ambient monomorphisms. -/
theorem perfectSupported_inflation_iff
    {K L : (perfectSupported j).FullSubcategory} (f : K ⟶ L) :
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
      (perfectSupported j)).inflation f ↔ Mono f.hom := by
  constructor
  · rintro ⟨Q, p, w, hS⟩
    exact hS.mono_f
  · intro hf
    let : Mono f.hom := hf
    let S := ShortComplex.mk f.hom (cokernel.π f.hom) (cokernel.condition f.hom)
    have hS : S.ShortExact := { exact := ShortComplex.cokernelSequence_exact f.hom }
    exact ⟨⟨cokernel f.hom, perfectSupported_X₃_of_shortExact j hS K.property L.property⟩,
      ObjectProperty.homMk (cokernel.π f.hom),
      ObjectProperty.hom_ext _ (cokernel.condition f.hom), hS⟩

/-- Admissible epimorphisms are exactly the actual ambient epimorphisms. -/
theorem perfectSupported_deflation_iff
    {K L : (perfectSupported j).FullSubcategory} (f : K ⟶ L) :
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
      (perfectSupported j)).deflation f ↔ Epi f.hom := by
  constructor
  · rintro ⟨Q, i, w, hS⟩
    exact hS.epi_g
  · intro hf
    let : Epi f.hom := hf
    let S := ShortComplex.mk (kernel.ι f.hom) f.hom (kernel.condition f.hom)
    have hS : S.ShortExact := { exact := ShortComplex.kernelSequence_exact f.hom }
    exact ⟨⟨kernel f.hom, perfectSupported_X₁_of_shortExact j hS K.property L.property⟩,
      ObjectProperty.homMk (kernel.ι f.hom),
      ObjectProperty.hom_ext _ (kernel.condition f.hom), hS⟩

/-- The opposite structure on the literal supported category. -/
def perfectSupportedOppositeWaldhausen :
    Waldhausen.Structure (perfectSupported j).FullSubcategoryᵒᵖ :=
  Waldhausen.oppositeComplexSubcategory (perfectSupported j)

/-- Opposite cofibrations retain precisely the underlying epimorphisms. -/
theorem perfectSupportedOppositeWaldhausen_cof_iff
    {K L : (perfectSupported j).FullSubcategoryᵒᵖ} (f : K ⟶ L) :
    (perfectSupportedOppositeWaldhausen j).cof f ↔ Epi f.unop.hom :=
  perfectSupported_deflation_iff j f.unop

/-- Duality is compatible with the original supported ambient-monomorphism structure. -/
theorem perfectSupportedOppositeWaldhausen_compatible :
    Waldhausen.IsCompatibleDual (perfectSupportedWaldhausen j)
      (perfectSupportedOppositeWaldhausen j) := by
  apply Waldhausen.exactDualStructure_compatible
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
      (perfectSupported j)) (perfectSupportedWaldhausen j)
    (Waldhausen.complexSubcategoryPullbackGluing (perfectSupported j))
  funext K L f
  exact propext (perfectSupported_inflation_iff j f).symm

/-- Support survives shifts by shifting the genuine quasi-isomorphism from zero. -/
theorem perfectSupported_shift_of_quasiIso_zero {E : CochainComplex X.Modules ℤ}
    (hE : perfectSupported j E) (n : ℤ) : perfectSupported j (E⟦n⟧) := by
  refine ⟨RingedSpace.isPerfectComplex_shift X.toRingedSpace hE.1 n, ?_⟩
  let R := (restrictFunctor j).mapHomologicalComplex (.up ℤ)
  have h : QuasiIso (0 : (0 : CochainComplex U.Modules ℤ) ⟶ R.obj E) := by
    rw [quasiIso_iff]
    exact fun k => (quasiIsoAt_iff_exactAt _ k
      (acyclic_of_isZero _ (isZero_zero _) k)).2 (hE.2 k)
  have hz := (shiftFunctor (CochainComplex U.Modules ℤ) n).map_isZero (isZero_zero _)
  have hs : (R.obj E⟦n⟧).Acyclic := fun k =>
    (exactAt_iff_of_quasiIsoAt
      ((shiftFunctor (CochainComplex U.Modules ℤ) n).map
        (0 : (0 : CochainComplex U.Modules ℤ) ⟶ R.obj E)) k).1
      (acyclic_of_isZero _ hz k)
  exact fun k => (exactAt_iff_of_quasiIsoAt ((R.commShiftIso n).app E).hom k).2 (hs k)

/-- Genuine opposite joint cylinders on the actual supported category. -/
def perfectSupportedOppositeJointData : Waldhausen.Fibration.RowFactorization.JointData
    (Waldhausen.Fibration.NestedWeakEquivalences.refl (perfectSupportedOppositeWaldhausen j)) := by
  exact Waldhausen.oppositeComplexJointData (perfectSupported j)
    (fun _ h => perfectSupported_shift_of_quasiIso_zero j h (-1))

/-- The literal supported restriction is exact for the actual opposite structures. -/
theorem perfectSupportedRestrict_op_isExact (T : X.Opens) :
    Waldhausen.IsExact (perfectSupportedOppositeWaldhausen T.ι).cof
      (perfectSupportedOppositeWaldhausen T.ι).weq
      (perfectSupportedOppositeWaldhausen (j ⁻¹ᵁ T).ι).cof
      (perfectSupportedOppositeWaldhausen (j ⁻¹ᵁ T).ι).weq
      (perfectSupportedRestrict j T).op :=
  Waldhausen.complexSubcategoryMap_op_exact (restrictFunctor j)
    (perfectSupported T.ι) (perfectSupported (j ⁻¹ᵁ T).ι)
    (fun _ h => perfectSupported_restrict j T h)

end AlgebraicGeometry.Scheme.Modules
