/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Complex
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusParameter
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedWindow

/-!
# Signed shift of the transfer parameter map

The degree-zero cochain parameter map goes from weight `q` to the
next weight with its actual coefficient quotient. Reindexing by the
torus commutes with the signed cochain shift, so the target has the
additional shift by one in motivic placement.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "B" => SheafWithTransfers.torusSectionsFunctor k

/-- Add the native cochain shift of weight one after the original
degree-zero parameter comparison. -/
def shiftTorusParameterMap {K L : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ}
    (s t : ℤ) (h : t + 1 = s) (f : K ⟶ ((B).mapHomologicalComplex (.up ℤ)).obj L) :
    K⟦s⟧ ⟶ ((B).mapHomologicalComplex (.up ℤ)).obj (L⟦t⟧⟦(1 : ℤ)⟧) :=
  let C := CochainComplex (SheafWithTransfers.{u + 1} k) ℤ
  let U := (B).mapHomologicalComplex (.up ℤ)
  (shiftFunctor C s).map f ≫ ((B).mapCochainComplexShiftIso s).inv.app L ≫
    U.map ((shiftFunctorAdd' C t 1 s h).hom.app L)

/-- The signed parameter product with its original transfers and
weight-one shift of the target. -/
def motivicTransferParameterProduct (q : ℕ) :
    motivicComplex k q ⟶ ((B).mapHomologicalComplex (.up ℤ)).obj
      ((motivicComplex k (q + 1))⟦(1 : ℤ)⟧) :=
  let Q := reducedTorus k (q + 1)
  shiftTorusParameterMap k (-(q : ℤ)) (-((q + 1 : ℕ) : ℤ)) (by omega)
    ((singularSheafCochainFunctor k 0).map (reducedTorusParameterProduct k q) ≫
      SheafWithTransfers.singularSheafCochainTorusSectionsMap k Q)

/-- Expand the actual signed parameter map at its literal source and target. -/
theorem motivicTransferParameterProduct_eq_shiftTorusParameterMap (q : ℕ) :
    let Q := reducedTorus k (q + 1)
    let s := -(q : ℤ)
    let t := -((q + 1 : ℕ) : ℤ)
    let h : t + 1 = s := by dsimp [s, t]; omega
    motivicTransferParameterProduct k q =
      shiftTorusParameterMap k s t h
        ((singularSheafCochainFunctor k 0).map (reducedTorusParameterProduct k q) ≫
          SheafWithTransfers.singularSheafCochainTorusSectionsMap k Q) := rfl

end AlgebraicGeometry.PresheafWithTransfers
