/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Divisors.Meromorphic.RegularTensorQuotient

/-! The ordinary quotient and its literal recovery work on arbitrary schemes. -/

open CategoryTheory AlgebraicGeometry Opposite

universe u

noncomputable section

variable (X : Scheme.{u}) (L N : X.Modules) (b : N.sections) (U : X.Opens)

example [IsIso ((N.unitHomEquiv.symm b).over U)] (a : Γ(Scheme.Modules.tensorObj L N, U)) :
    Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U) L N
      (Scheme.Modules.regularTensorQuotientOnOpen X L N b U a) (b.eval (op U)) = a :=
  Scheme.Modules.tensorSection_regularTensorQuotientOnOpen X L N b U a

example [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N]
    (a : Γ(Scheme.Modules.tensorObj L N, ⊤)) :
    let V := Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) N b
    Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op V) L N
      (Scheme.Modules.regularTensorQuotientOnNonvanishingOpen X L N b a) (b.eval (op V)) =
      (Scheme.Modules.tensorObj L N).presheaf.map (homOfLE le_top).op a :=
  Scheme.Modules.tensorSection_regularTensorQuotientOnNonvanishingOpen X L N b a

#print axioms AlgebraicGeometry.Scheme.Modules.tensorSectionQuotientIsoOver_inv_apply
#print axioms AlgebraicGeometry.Scheme.Modules.tensorSection_regularTensorQuotientOnOpen
#print axioms AlgebraicGeometry.Scheme.Modules.tensorSection_regularTensorQuotientOnNonvanishingOpen
