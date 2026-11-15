/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.Algebra.Homology.Monoidal
public import StacksFrontier.Homology.KFlat.BifunctorToTotalComplex
/-! # K-flatness of the native cochain tensor unit -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
namespace CochainComplex.KFlatBifunctor
variable {C : Type*} [Category C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasCoproducts.{0} C]

/-- The standard K-flat tensor-unit argument, expressed with the native complex
unit rather than requiring a full monoidal-category instance on all cochains.
This is the weak-assumption form of `KFlatMonoidal.kFlat_tensorUnit`. -/
theorem kFlat_nativeTensorUnit :
    KFlat (curriedTensor C) (HomologicalComplex.tensorUnit C (.up ℤ)) := by
  intro G hG n
  exact HomologicalComplex.ExactAt.of_iso (hG n)
    (HomologicalComplex.rightUnitor G).symm

variable [HasDerivedCategory C]
  [(kFlatQLeft (curriedTensor C)).IsLocalization (kFlatQuasiIsoLeft (curriedTensor C))]
  [(kFlatQ (curriedTensor C)).IsLocalization (kFlatQuasiIso (curriedTensor C))]
  (hres : ∀ G : CochainComplex C ℤ, ∃ (P : CochainComplex C ℤ) (f : P ⟶ G),
    KFlat (curriedTensor C) P ∧ QuasiIso f)

/-- The original derived-to-ordinary tensor comparison with the native unit is
invertible for any first factor; no K-flatness or boundedness of that factor is needed. -/
theorem isIso_toTensor_nativeUnit (K : CochainComplex C ℤ) :
    IsIso (toTensor (curriedTensor C) hres K
      (HomologicalComplex.tensorUnit C (.up ℤ))) := by
  rw [toTensor_eq_comparisonRight (curriedTensor C) hres K
    (kFlat_nativeTensorUnit (C := C))]
  infer_instance

end CochainComplex.KFlatBifunctor
