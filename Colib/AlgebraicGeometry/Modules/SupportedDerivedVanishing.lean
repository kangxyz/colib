/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.SupportedDerivedLift

/-! # Actual acyclicity and derived vanishing for supported complexes -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

universe u d

variable {X : Scheme.{u}} [HasDerivedCategory.{d} X.Modules]

/-- Derived vanishing detects actual homology of the original complex. -/
theorem acyclic_iff_isZero_derived (K : CochainComplex X.Modules ℤ) :
    K.Acyclic ↔ IsZero (DerivedCategory.Q.obj K) := by
  constructor
  · intro hK
    have : QuasiIso (0 : (0 : CochainComplex X.Modules ℤ) ⟶ K) := by
      rw [quasiIso_iff]
      intro n
      exact (quasiIsoAt_iff_exactAt' _ n (hK n)).2
        (acyclic_of_isZero _ (isZero_zero _) n)
    exact ((asIso (DerivedCategory.Q.map (0 : (0 : CochainComplex X.Modules ℤ) ⟶ K))).isZero_iff).1
      (DerivedCategory.Q.map_isZero (isZero_zero _))
  · intro hK n
    rw [exactAt_iff_isZero_homology]
    exact (((DerivedCategory.homologyFunctorFactors X.Modules n).app K).isZero_iff).1
      ((DerivedCategory.homologyFunctor X.Modules n).map_isZero hK)

/-- Vanishing on an open is equivalent to vanishing under the actual derived restriction. -/
theorem restrictAcyclic_iff_isZero_derivedRestrict {U : Scheme.{u}}
    [HasDerivedCategory U.Modules] (j : U ⟶ X) [IsOpenImmersion j]
    (K : CochainComplex X.Modules ℤ) :
    (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj K).Acyclic ↔
      IsZero ((restrictFunctor j).mapDerivedCategory.obj (DerivedCategory.Q.obj K)) := by
  rw [acyclic_iff_isZero_derived]
  exact ((restrictFunctor j).mapDerivedCategoryFactors.app K).isZero_iff.symm

end AlgebraicGeometry.Scheme.Modules
