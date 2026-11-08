/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.QcqsGeometry

/-! # Regression tests for the native qcqs perfect restriction geometry -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.OpenDerivedImage

universe u d

variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j] [HasDerivedCategory.{d} U.Modules]

-- No roof, density, or complement hypothesis is supplied.
example : HasDerivedRoofs j := hasDerivedRoofs_of_qcqs j

example : HasPerfectComplements j := hasPerfectComplements_of_qcqs j

-- The fixed target need not be perfect. Actual quasi-coherent cohomology suffices.
example (K E : CochainComplex X.Modules ℤ)
    (hK : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K)
    (hE : ∀ i : ℤ,
      ((HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) i).obj E).IsQuasicoherent)
    (α : DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)) :
    ∃ (R : CochainComplex X.Modules ℤ) (q : R ⟶ K) (a : R ⟶ E),
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) R ∧
      QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map q) ∧
      DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map q) ≫ α =
        DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map a) :=
  exists_isPerfectComplex_chainMap_roof_of_qcqs j K E hK hE α

-- The complement is an actual complex, in the same arbitrary derived model on U.
example (P : CochainComplex U.Modules ℤ)
    (hP : RingedSpace.IsPerfectComplex (X := U.toRingedSpace) P) :
    ∃ (R : CochainComplex X.Modules ℤ) (C : CochainComplex U.Modules ℤ),
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) R ∧
      RingedSpace.IsPerfectComplex (X := U.toRingedSpace) C ∧
      Nonempty (DerivedCategory.Q.obj
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj R) ≅
        DerivedCategory.Q.obj (P ⊞ C)) :=
  exists_isPerfectComplex_restrict_complement j P hP
