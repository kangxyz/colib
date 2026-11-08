/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectScalarCofiberFunctor

/-! # The actual categorical scalar cofiber and its signed cone

The universal extension-category cofiber is compared to the literal signed cone
by its original quotient map. When the scalar restricts to the specified unit,
this comparison lives in the original relative-acyclic category.

Adapted from Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiber.lean:35-78,
ScalarCofiberPrism.lean:38-93 and
Quillen/Waldhausen/SplitComplexes/FactorizationCofiber.lean:40-91
at c561118b7795eb9780be9ed391c3251d6a4d0afd. The Waldhausen structure here is
native ambient Mono/QuasiIso, with no split-subcategory replacement.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Waldhausen Fibration
open CochainComplex CochainComplex.SplitFactorization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable (X : Scheme.{u}) (r : Γ(X, ⊤))

/-- The literal first factor as a genuine extension object of the native category. -/
def perfectScalarExtension
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    ExtensionCategory.Obj (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace) :=
  ⟨Arrow.mk ((perfectScalarInclusionNat X r).app K), perfectScalarInclusionNat_cof X r K⟩

/-- The original first factor of the actual scalar extension. -/
def perfectScalarInclusion
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :=
  (ExtensionCategory.inclusion (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).app
    (perfectScalarExtension X r K)

/-- The original weak projection of the same scalar extension. -/
def perfectScalarProjection
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :=
  (perfectScalarProjectionNat X r).app K

/-- The factors still compose to the forward scalar, not its inverse. -/
theorem perfectScalarInclusion_projection
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    perfectScalarInclusion X r K ≫ perfectScalarProjection X r K =
      (perfectGlobalScalar X r).app K :=
  NatTrans.congr_app (perfectScalarInclusionNat_projection X r) K

/-- The actual projection is fine weak before any open restriction. -/
theorem perfectScalarProjection_weak
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
      (perfectScalarProjection X r K) := perfectScalarProjectionNat_weak X r K

/-- The actual categorical cofiber is the original signed cone through its quotient. -/
def perfectScalarCofiberIso
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (ExtensionCategory.cofiber (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).obj
        (perfectScalarExtension X r K) ≅ (perfectScalarConeFunctor X r).obj K :=
  (ExtensionCategory.cofiber_isPushout
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace) (perfectScalarExtension X r
      K)).isoIsPushout
    _ _ (perfectScalarCone_isPushout X r K)

/-- The comparison transports the original quotient to exactly `quotientToCone`. -/
theorem perfectScalarCofiberIso_quotient
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (ExtensionCategory.quotient (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).app
        (perfectScalarExtension X r K) ≫ (perfectScalarCofiberIso X r K).hom =
      ObjectProperty.homMk (quotientToCone ((complexGlobalScalar X r).app K.obj)) :=
  (ExtensionCategory.cofiber_isPushout
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (perfectScalarExtension X r K)).inl_isoIsPushout_hom _ _ (perfectScalarCone_isPushout X r K)

variable {X} {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

include hq in
/-- Restriction detects the original first factor as weak via its actual scalar composite. -/
theorem perfectScalarInclusion_openWeak
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (perfectOpenNested j).coarse.weq (perfectScalarInclusion X r K) := by
  apply (perfectOpenNested j).coarse.weq.of_postcomp
    (perfectScalarInclusion X r K) (perfectScalarProjection X r K)
    ((perfectOpenNested j).le_weq _ (perfectScalarProjection_weak X r K))
  rw [perfectScalarInclusion_projection]
  exact quasiIso_restrict_complexGlobalScalar j r q hq K.obj

/-- The original first factor is the same cofibration after weak enlargement. -/
theorem perfectScalarInclusion_openCof
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (perfectOpenNested j).coarse.cof (perfectScalarInclusion X r K) :=
  perfectScalarInclusionNat_cof X r K

/-- The actual universal quotient retains its original chosen-zero pushout. -/
theorem perfectScalarCofiber_isPushout
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    IsPushout (perfectScalarInclusion X r K) (0 : K ⟶ (perfectOpenNested j).coarse.zero)
      ((ExtensionCategory.quotient (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).app
        (perfectScalarExtension X r K))
      (0 : (perfectOpenNested j).coarse.zero ⟶
        (ExtensionCategory.cofiber (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).obj
          (perfectScalarExtension X r K)) := by
  have h := ExtensionCategory.cofiber_isPushout
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace) (perfectScalarExtension X r K)
  convert h using 1 <;> first
    | rfl
    | exact (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).isZero.eq_of_tgt _ _
    | exact (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).isZero.eq_of_src _ _

/-- The same literal signed cone, with its actual relative-acyclic witness. -/
def perfectOpenScalarCone
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    AcyclicCategory (perfectOpenNested j) :=
  (perfectOpenScalarConeFunctor j r q hq).obj K

/-- The same original comparison to the supported cone's underlying perfect object. -/
def perfectOpenScalarCofiberIso
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (ExtensionCategory.cofiber (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).obj
      (perfectScalarExtension X r K) ≅ (perfectOpenScalarCone r j q hq K).obj :=
  perfectScalarCofiberIso X r K

/-- The original open-supported comparison retains the exact signed quotient. -/
theorem perfectOpenScalarCofiberIso_quotient
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (ExtensionCategory.quotient (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).app
        (perfectScalarExtension X r K) ≫ (perfectOpenScalarCofiberIso r j q hq K).hom =
      ObjectProperty.homMk (quotientToCone ((complexGlobalScalar X r).app K.obj)) :=
  perfectScalarCofiberIso_quotient X r K

/-- Adding the relative-acyclic witness leaves the literal scalar-cone object unchanged. -/
theorem perfectOpenScalarConeFunctor_obj
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (perfectOpenScalarConeFunctor j r q hq).obj K = perfectOpenScalarCone r j q hq K := rfl

/-- The actual categorical cofiber lies in the original relative-acyclic category. -/
def perfectOpenScalarCofiberAcyclic
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    AcyclicCategory (perfectOpenNested j) :=
  ⟨(ExtensionCategory.cofiber (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).obj
      (perfectScalarExtension X r K),
    acyclic_of_iso (perfectOpenNested j).coarse (perfectOpenScalarCone r j q hq K).property
      (perfectOpenScalarCofiberIso r j q hq K).symm⟩

/-- The quotient-preserving comparison is an isomorphism in the actual acyclic category. -/
def perfectOpenScalarCofiberAcyclicIso
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    perfectOpenScalarCofiberAcyclic r j q hq K ≅ perfectOpenScalarCone r j q hq K :=
  (acyclicObjects (perfectOpenNested j)).isoMk (perfectOpenScalarCofiberIso r j q hq K)

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0303",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiber.lean:35-69"
    "adaptation" "The actual categorical cofiber, signed quotient and relative-acyclic isomorphism"]
  AlgebraicGeometry.Scheme.Modules.perfectScalarCofiberIso
  AlgebraicGeometry.Scheme.Modules.perfectScalarCofiberIso_quotient
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCofiberAcyclicIso
