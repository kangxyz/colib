/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.RelativeCurve.Pencils.ConstantFamily
open CategoryTheory AlgebraicGeometry Stacks.Divisors
open AlgebraicGeometry.Scheme.PolynomialSectionPencil
universe u
variable {R : Type u} [CommRing R] {X C : Scheme.{u}}
  (b : X ⟶ Spec (.of R)) (p : C ⟶ X) (L : C.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L]
  (s : Γ(L, ⊤))
example [IsFinite ((zeroScheme C L s).subschemeι ≫ p)] :
    IsFinite (familySource b p L s s) := isFinite_constantFamilySource b p L s
example [Flat ((zeroScheme C L s).subschemeι ≫ p)] :
    Flat (familySource b p L s s) := flat_constantFamilySource b p L s
#check familyZero_constant
#check constantFamilySupportIso_hom_fst
