/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.DerivedCechCone
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections

/-! # The signed Čech complex over the coefficient ring -/

public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace AlgebraicGeometry.projectiveSpaceOver

attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts

variable (R : CommRingCat.{u}) (M : (line R).Modules)

/-- The degree-zero cochain map induced by the actual signed difference of chart sections. -/
@[expose] def lineCechSectionsMap :=
  (single (ModuleCat.{u} R) (.up ℤ) 0).map
    ((globalSectionsOver (lineProjection R)).map
      (Scheme.Modules.twoOpenCech (lineChartZero R) (lineChartOne R) M).g)

/-- The signed Čech cochain complex of sections, in degrees zero and one. -/
@[expose] def lineCechSectionsComplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  (CochainComplex.mappingCone (lineCechSectionsMap R M))⟦(-1 : ℤ)⟧

/-- The signed complex is zero in negative degrees. -/
theorem lineCechSectionsComplex_isStrictlyGE :
    (lineCechSectionsComplex R M).IsStrictlyGE 0 := by
  let C := CochainComplex.mappingCone (lineCechSectionsMap R M)
  let : C.IsStrictlyGE (-1) := by
    refine (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi ↦ ?_
    apply (CochainComplex.mappingCone.isZero_X_iff _ i).2
    exact ⟨isZero_single_obj_X _ _ _ _ (by omega),
      isZero_single_obj_X _ _ _ _ (by omega)⟩
  exact C.isStrictlyGE_shift (-1) (-1) 0 (by omega)

/-- The signed complex is zero in degrees greater than one. -/
theorem lineCechSectionsComplex_isStrictlyLE :
    (lineCechSectionsComplex R M).IsStrictlyLE 1 := by
  let C := CochainComplex.mappingCone (lineCechSectionsMap R M)
  let : C.IsStrictlyLE 0 := by
    refine (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi ↦ ?_
    apply (CochainComplex.mappingCone.isZero_X_iff _ i).2
    exact ⟨isZero_single_obj_X _ _ _ _ (by omega),
      isZero_single_obj_X _ _ _ _ (by omega)⟩
  exact C.isStrictlyLE_shift 0 (-1) 1 (by omega)

end AlgebraicGeometry.projectiveSpaceOver
