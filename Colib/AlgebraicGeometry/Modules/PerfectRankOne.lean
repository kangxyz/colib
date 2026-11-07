/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectWaldhausen
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StructureSheafDegreeZero

/-!
# The structure sheaf as a native perfect complex

The rank-one object is the actual structure sheaf in degree zero, in the full subcategory
specified by Stacks perfectness. No replacement category or local-perfect model is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The structure sheaf in any single degree is a native perfect complex. -/
theorem Complex.isPerfectComplex_single_unit (X : Scheme.{u}) (n : ℤ) :
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
      ((CochainComplex.singleFunctor X.Modules n).obj
        (SheafOfModules.unit X.ringCatSheaf)) :=
  RingedSpace.isPerfectComplex_of_isStrictlyPerfect
    (StrictlyPerfect.isStrictlyPerfect_single
      (StrictlyPerfect.isDirectSummandOfFiniteFree_structureModule X.toRingedSpace) n)

/-- The rank-one structure sheaf in degree zero, as its actual native perfect complex. -/
def rankOnePerfectComplex (X : Scheme.{u}) :
    ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
  ⟨(CochainComplex.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf),
    Complex.isPerfectComplex_single_unit X 0⟩

/-- Forgetting perfectness gives the original structure-sheaf single complex. -/
@[simp]
theorem rankOnePerfectComplex_obj (X : Scheme.{u}) :
    (rankOnePerfectComplex X).obj =
      (CochainComplex.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf) :=
  rfl

end AlgebraicGeometry.Scheme.Modules
