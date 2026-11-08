/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.PerfectScalarCone

/-! Regression clients retain the native structures, signed quotient and actual cone maps. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Waldhausen Fibration CochainComplex.SplitFactorization
universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

example {K L : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))} (f : K ⟶ L) :
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof f ↔ Mono f.hom := Iff.rfl

example {K L : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))} (f : K ⟶ L) :
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq f ↔ QuasiIso f.hom := Iff.rfl

example {K L : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))} (f : K ⟶ L) :
    (((perfectOpenScalarConeFunctor j r q hq).map f).hom).hom =
      CochainComplex.mappingCone.map ((complexGlobalScalar X r).app K.obj)
        ((complexGlobalScalar X r).app L.obj) f.hom f.hom
        ((complexGlobalScalar X r).naturality f.hom).symm := rfl

example (K : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (ExtensionCategory.quotient (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).app
        (perfectScalarExtension X r K) ≫ (perfectScalarCofiberIso X r K).hom =
      ObjectProperty.homMk (quotientToCone ((complexGlobalScalar X r).app K.obj)) :=
  perfectScalarCofiberIso_quotient X r K

example (K : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    perfectScalarInclusion X r K ≫ perfectScalarProjection X r K =
      (perfectGlobalScalar X r).app K := perfectScalarInclusion_projection X r K

example (K : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    perfectOpenScalarConeKMap j r q hq 0
        ((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kZeroObjectClass K) =
      (acyclicStructure (perfectOpenNested j)).kZeroObjectClass
        (perfectOpenScalarCone r j q hq K) :=
  perfectOpenScalarConeKMap_objectClass j r q hq K

example (K : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (acyclicStructure (perfectOpenNested j)).kZeroObjectClass
        (perfectOpenScalarCofiberAcyclic r j q hq K) =
      (acyclicStructure (perfectOpenNested j)).kZeroObjectClass
        (perfectOpenScalarCone r j q hq K) :=
  perfectOpenScalarCofiberAcyclic_class j r q hq K
