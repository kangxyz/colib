/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Homology.TensorUnitKFlat
/-! # Original derived tensor comparison on a native unit-coordinate insertion -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
namespace CochainComplex.KFlatBifunctor
variable {C : Type*} [Category C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasCoproducts.{0} C] [HasDerivedCategory C]
  [(kFlatQLeft (curriedTensor C)).IsLocalization (kFlatQuasiIsoLeft (curriedTensor C))]
  [(kFlatQ (curriedTensor C)).IsLocalization (kFlatQuasiIso (curriedTensor C))]
  (hres : ∀ G : CochainComplex C ℤ, ∃ (P : CochainComplex C ℤ) (f : P ⟶ G),
    KFlat (curriedTensor C) P ∧ QuasiIso f)

local instance (K : CochainComplex C ℤ) :
    IsIso (toTensor (curriedTensor C) hres K
      (HomologicalComplex.tensorUnit C (.up ℤ))) :=
  isIso_toTensor_nativeUnit hres K

/-- The original `toTensor` comparison recovers the localized native insertion
from its genuine two-input derived tensor map and the unit comparison inverse.
No invertibility of the comparison at the target pair is required. -/
theorem toTensor_unitCoordinate {K L M : CochainComplex C ℤ}
    (a : K ⟶ L) (b : HomologicalComplex.tensorUnit C (.up ℤ) ⟶ M) :
    DerivedCategory.Q.map (HomologicalComplex.rightUnitor K).inv ≫
      inv (toTensor (curriedTensor C) hres K
        (HomologicalComplex.tensorUnit C (.up ℤ))) ≫
      ((derivedBifunctor (curriedTensor C)).map (DerivedCategory.Q.map a)).app
        (DerivedCategory.Q.obj (HomologicalComplex.tensorUnit C (.up ℤ))) ≫
      ((derivedBifunctor (curriedTensor C)).obj (DerivedCategory.Q.obj L)).map
        (DerivedCategory.Q.map b) ≫ toTensor (curriedTensor C) hres L M =
    DerivedCategory.Q.map ((HomologicalComplex.rightUnitor K).inv ≫
      HomologicalComplex.tensorHom a b) := by
  rw [toTensor_naturality]
  simp only [IsIso.inv_hom_id_assoc, ← Functor.map_comp]

end CochainComplex.KFlatBifunctor
