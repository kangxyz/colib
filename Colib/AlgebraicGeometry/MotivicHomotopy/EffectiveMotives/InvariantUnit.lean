/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Representable
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.InvariantUnit

/-!
# Effective representatives of invariant coefficients

The original singular unit is a quasi-isomorphism on an invariant transfer
presheaf. Exact Nisnevich sheafification and the single-complex comparison
identify its effective representative with the sheaf in degree zero.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers

variable (k : Type u) [Field k]
variable [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

/-- The original sheafified singular unit on a coefficient. -/
def singularDerivedUnitApp (P : PresheafWithTransfers.{u + 1} k) :
    (DerivedCategory.singleFunctor (SheafWithTransfers.{u + 1} k) 0).obj
      ((nisnevichSheafify k).obj P) ⟶
    (effectiveMotivesMinusToDerived k).obj ((singularEffectiveMotiveFunctor k).obj P) :=
  let a := nisnevichSheafify k
  let e := (HomologicalComplex.singleMapHomologicalComplex a (.up ℤ) 0).app P
  ((DerivedCategory.singleFunctorIsoCompQ (SheafWithTransfers.{u + 1} k) 0).app
      (a.obj P)).hom ≫
    DerivedCategory.Q.map (e.inv ≫ (a.mapHomologicalComplex (.up ℤ)).map (singularCochainUnitApp P))

/-- The actual degree-zero coefficient maps isomorphically to its singular
effective representative when its original affine projection is invertible. -/
theorem isIso_singularDerivedUnitApp (P : PresheafWithTransfers.{u + 1} k)
    (hP : P.IsA1Invariant) : IsIso (singularDerivedUnitApp k P) := by
  let a := nisnevichSheafify k
  let e := (HomologicalComplex.singleMapHomologicalComplex a (.up ℤ) 0).app P
  let f := singularCochainUnitApp P
  let : QuasiIso f := singularCochainUnitApp_quasiIso P hP
  let g := (a.mapHomologicalComplex (.up ℤ)).map f
  let : QuasiIso g := inferInstance
  change IsIso (((DerivedCategory.singleFunctorIsoCompQ (SheafWithTransfers.{u + 1} k) 0).app
      (a.obj P)).hom ≫ DerivedCategory.Q.map (e.inv ≫ g))
  infer_instance

end AlgebraicGeometry.MotivicHomotopy
