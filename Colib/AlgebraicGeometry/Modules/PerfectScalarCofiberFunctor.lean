/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectScalarConeWaldhausen
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.FactorizationConeFunctor
public import Colib.CategoryTheory.Waldhausen.GilletWaldhausen.ExactFunctorSequence
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Cofiber

/-! # The native scalar cylinder and its actual signed cofiber sequence

The middle object is the original identity-cone biproduct, the first factor is
its original inclusion, and the quotient is the original quotient followed by
`mappingConeNegIso`. The relative cofibration condition uses every ambient
monomorphism, not merely split cofibrations. All structures are the preexisting
native perfect-complex structures.

Adapted from Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberFunctor.lean:41-159
and ScalarCofiberPrism.lean:38-58 at c561118b7795eb9780be9ed391c3251d6a4d0afd.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CochainComplex CochainComplex.SplitFactorization Waldhausen
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable (X : Scheme.{u}) (r : Γ(X, ⊤))

local instance : HasFiniteBiproducts
    (CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) ℤ) :=
  Abelian.hasFiniteBiproducts
    (C := CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) ℤ)

local instance : HasFiniteBiproducts (CochainComplex X.Modules ℤ) :=
  Abelian.hasFiniteBiproducts (C := CochainComplex X.Modules ℤ)

local instance : ObjectProperty.ContainsZero
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
  RingedSpace.isPerfectComplex_containsZero X.toRingedSpace

local instance : ObjectProperty.IsClosedUnderIsomorphisms
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
  RingedSpace.isPerfectComplex_closedUnderIsomorphisms X.toRingedSpace

local instance : (abelianExactStructure
      (CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) ℤ)).IsExtensionClosed
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
  RingedSpace.isPerfectComplex_extensionClosed X.toRingedSpace

local instance : ObjectProperty.IsClosedUnderFiniteProducts
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
  RingedSpace.isPerfectComplex_closedUnderFiniteProducts X.toRingedSpace

local instance : HasFiniteBiproducts
    (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :=
  ExactSubcategory.subcategoryHasFiniteBiproducts
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))

/-- The original scalar cylinder middle object and its actual coefficient maps. -/
def perfectScalarMiddleFunctor :
    ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) ⥤
      ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
  ObjectProperty.lift (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))
    (middleNatTransFunctor (Functor.whiskerRight (perfectGlobalScalar X r)
      (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
    (fun K => middle_property (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))
      (RingedSpace.perfectComplexes_coneClosed X.toRingedSpace)
      K.property K.property ((complexGlobalScalar X r).app K.obj))

instance perfectScalarMiddleFunctor_additive : (perfectScalarMiddleFunctor X r).Additive := by
  unfold perfectScalarMiddleFunctor
  infer_instance

/-- The actual first factor, natural in the original perfect complex. -/
def perfectScalarInclusionNat :
    𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) ⟶
      perfectScalarMiddleFunctor X r where
  app K := ObjectProperty.homMk (inclusion ((complexGlobalScalar X r).app K.obj))
  naturality _ _ g := ObjectProperty.hom_ext _
    ((inclusionNatTrans (Functor.whiskerRight (perfectGlobalScalar X r)
      (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))))).naturality g)

/-- The actual fine weak projection, without changing its target. -/
def perfectScalarProjectionNat : perfectScalarMiddleFunctor X r ⟶
    𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) where
  app K := ObjectProperty.homMk (projection ((complexGlobalScalar X r).app K.obj))
  naturality _ _ g := ObjectProperty.hom_ext _
    ((projectionNatTrans (Functor.whiskerRight (perfectGlobalScalar X r)
      (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))))).naturality g)

/-- The literal signed quotient into the original scalar cone. -/
def perfectScalarConeProjectionNat :
    perfectScalarMiddleFunctor X r ⟶ perfectScalarConeFunctor X r where
  app K := ObjectProperty.homMk (quotientToCone ((complexGlobalScalar X r).app K.obj))
  naturality _ _ g := ObjectProperty.hom_ext _
    ((quotientToConeNatTrans (Functor.whiskerRight (perfectGlobalScalar X r)
      (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))))).naturality g)

/-- The two factors compose to the actual forward scalar endomorphism. -/
theorem perfectScalarInclusionNat_projection :
    perfectScalarInclusionNat X r ≫ perfectScalarProjectionNat X r = perfectGlobalScalar X r := by
  apply NatTrans.ext
  funext K
  exact ObjectProperty.hom_ext _ (inclusion_projection ((complexGlobalScalar X r).app K.obj))

/-- The original first factor followed by the sign-adjusted quotient is zero. -/
theorem perfectScalarInclusionNat_quotient :
    perfectScalarInclusionNat X r ≫ perfectScalarConeProjectionNat X r = 0 := by
  apply NatTrans.ext
  funext K
  exact ObjectProperty.hom_ext _ (inclusion_quotientToCone ((complexGlobalScalar X r).app K.obj))

/-- The scalar middle functor preserves actual ambient short exact sequences. -/
theorem perfectScalarMiddleFunctor_shortExact
    (S : ShortComplex
      (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))))
    (hS : (S.map (ObjectProperty.ι
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))).ShortExact) :
    ((S.map (perfectScalarMiddleFunctor X r)).map (ObjectProperty.ι
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))).ShortExact :=
  middleNatTransFunctor_shortExact
    (Functor.whiskerRight (perfectGlobalScalar X r)
      (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))) S hS hS

/-- All original ambient cofibrations, weak equivalences and pushouts are preserved. -/
theorem perfectScalarMiddleFunctor_waldhausenExact :
    IsExact (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
      (perfectScalarMiddleFunctor X r) :=
  RingedSpace.perfectComplexes_lift_isExact X.toRingedSpace _
    (RingedSpace.perfectComplexes_cofibrationClosed X.toRingedSpace) _
    (perfectScalarMiddleFunctor_shortExact X r) (fun g hg => by
      let φ := Arrow.homMk (f := Arrow.mk ((complexGlobalScalar X r).app _))
        (g := Arrow.mk ((complexGlobalScalar X r).app _))
        g.hom g.hom ((complexGlobalScalar X r).naturality g.hom)
      let : QuasiIso φ.right := hg
      exact middleFunctor_map_quasiIso φ)

/-- Every actual scalar projection is already weak before restriction. -/
theorem perfectScalarProjectionNat_weak
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
      ((perfectScalarProjectionNat X r).app K) :=
  projection_quasiIso ((complexGlobalScalar X r).app K.obj)

/-- The literal signed pointwise sequence with all three original objects. -/
def perfectScalarConeSequence
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :=
  exactFunctorSequenceAt (perfectScalarInclusionNat X r) (perfectScalarConeProjectionNat X r)
    (perfectScalarInclusionNat_quotient X r) K

/-- The pointwise sequence is an inherited ambient short exact sequence. -/
theorem perfectScalarConeSequence_conflation
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (ExactSubcategory.exactStructure (abelianExactStructure
      (CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) ℤ))
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))).conflation
      (perfectScalarConeSequence X r K) :=
  quotientToConeSequence_shortExact ((complexGlobalScalar X r).app K.obj)

/-- The first factor is an actual ambient monomorphism. -/
theorem perfectScalarInclusionNat_cof
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof
      ((perfectScalarInclusionNat X r).app K) :=
  (quotientToConeSequence_shortExact ((complexGlobalScalar X r).app K.obj)).mono_f

/-- Quotient exactness gives the genuine relative ambient-monomorphism condition. -/
theorem perfectScalarInclusionNat_cofibration :
    Additivity.IsCofibrationTransformation
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
      (perfectScalarInclusionNat X r)
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace) where
  app_cof := perfectScalarInclusionNat_cof X r
  relative_cof {K L} g hg := by
    let E := ExactSubcategory.exactStructure (abelianExactStructure
      (CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) ℤ))
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))
    let : HasPushout
        (exactFunctorSequenceAt (perfectScalarInclusionNat X r) (perfectScalarConeProjectionNat X r)
          (perfectScalarInclusionNat_quotient X r) K).f
        (exactFunctorSequenceMap (perfectScalarInclusionNat X r)
          (perfectScalarConeProjectionNat X r) (perfectScalarInclusionNat_quotient X r) g).τ₁ :=
      Additivity.hasPushout (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
        (perfectScalarInclusionNat X r) (perfectScalarInclusionNat_cof X r) g
    apply (RingedSpace.perfectComplexes_inflation_iff X.toRingedSpace _).1
    exact relativePushout_inflation
      (C := ObjectProperty.FullSubcategory
        (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) E
      (exactFunctorSequenceMap (perfectScalarInclusionNat X r) (perfectScalarConeProjectionNat X r)
        (perfectScalarInclusionNat_quotient X r) g)
      (perfectScalarConeSequence_conflation X r K) (perfectScalarConeSequence_conflation X r L)
      ((RingedSpace.perfectComplexes_inflation_iff X.toRingedSpace _).2
        ((perfectScalarConeFunctor_waldhausenExact X r).cofibration g hg))

/-- The signed quotient gives the actual chosen-zero pushout, not a replacement cone. -/
theorem perfectScalarCone_isPushout
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    IsPushout ((perfectScalarInclusionNat X r).app K)
      ((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).isZero.from_ K)
      ((perfectScalarConeProjectionNat X r).app K)
      ((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).isZero.to_
        ((perfectScalarConeFunctor X r).obj K)) :=
  isPushout_of_isColimit_cokernel _
    ((ExactSubcategory.exactStructure (abelianExactStructure
      (CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) ℤ))
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))).cokernel _
        (perfectScalarConeSequence_conflation X r K))
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).isZero _ _

/-- The original scalar cylinder and signed cone form a genuine cofibration sequence. -/
theorem perfectScalarCofibrationSequence :
    Additivity.IsCofibrationSequence
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
      (perfectScalarInclusionNat X r) (perfectScalarConeProjectionNat X r) where
  exactF := IsExact.id _ _
  exactG := perfectScalarMiddleFunctor_waldhausenExact X r
  exactH := perfectScalarConeFunctor_waldhausenExact X r
  cofibration := perfectScalarInclusionNat_cofibration X r
  cofiber := perfectScalarCone_isPushout X r

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0303",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberFunctor.lean:114-159"
    "adaptation" "The original signed sequence, with native ambient Mono cofibrations"]
  AlgebraicGeometry.Scheme.Modules.perfectScalarInclusionNat_cofibration
  AlgebraicGeometry.Scheme.Modules.perfectScalarCofibrationSequence
