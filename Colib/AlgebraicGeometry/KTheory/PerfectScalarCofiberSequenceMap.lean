/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectScalarCofiber
public import Colib.KTheory.Waldhausen.Additivity.IdentitySequence
public import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberMap

/-!
# The literal identity-to-scalar map of cofibration sequences

The source is identity-to-identity-to-the-chosen-zero. The target is the original scalar
cylinder with its signed literal cone. Vertical components are identity, the original inclusion,
and exactly the zero-to-acyclic-inclusion transformation whiskered by the actual acyclic cone
functor. All inherited cofibrations and the original fine weak projection remain unchanged.
Implementation provenance:
    Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberSequenceMap.lean:34-86
at c561118b7795eb9780be9ed391c3251d6a4d0afd.
These are categorical input data for a separately constructed based-additivity square.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
    CategoryTheory.Waldhausen.Fibration
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The source sequence uses the exact original chosen-zero map in the coarse structure. -/
theorem perfectOpenScalarIdentityCofibrationSequence :
    IsCofibrationSequence (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
      (perfectOpenNested j).coarse
      (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
        X.toRingedSpace))))) (QuotientRows.oneIdToZero (perfectOpenNested j).coarse) :=
  identityCofibrationSequence (perfectOpenNested j).coarse (𝟭 (ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))))
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace) (changeWeak_exact (perfectOpenNested
      j))

/-- The target retains the original cylinder, signed cone and inherited relative cofibrations. -/
theorem perfectOpenScalarCofibrationSequence (r : Γ(X, ⊤)) :
    IsCofibrationSequence (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
      (perfectOpenNested j).coarse
      (perfectScalarInclusionNat X r) (perfectScalarConeProjectionNat X r) :=
  let hs := perfectScalarCofibrationSequence X r
  { exactF := hs.exactF.comp (changeWeak_exact (perfectOpenNested j))
    exactG := hs.exactG.comp (changeWeak_exact (perfectOpenNested j))
    exactH := hs.exactH.comp (changeWeak_exact (perfectOpenNested j))
    cofibration :=
      { app_cof := hs.cofibration.app_cof
        relative_cof f hf := hs.cofibration.relative_cof f hf }
    cofiber := hs.cofiber }

variable (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The quotient component is the original zero-to-inclusion on the actual cone functor. -/
def perfectOpenScalarZeroToCone :
    zeroFunctor (C := ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
      X.toRingedSpace))) (perfectOpenNested j).coarse ⟶ perfectScalarConeFunctor X r :=
  Functor.whiskerLeft (perfectOpenScalarConeFunctor j r q hq)
    (zeroToAcyclicInclusion (perfectOpenNested j))

/-- Every component retains the specified coarse zero and the same literal scalar cone. -/
theorem perfectOpenScalarZeroToCone_app (K : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (perfectOpenScalarZeroToCone j r q hq).app K =
      (perfectOpenNested j).coarse.isZero.to_ ((perfectScalarConeFunctor X r).obj K) := rfl

/-- The entire quotient square is the reversed commutation of the original zero-corner pushout. -/
theorem perfectOpenScalarZeroToCone_sequence :
    QuotientRows.oneIdToZero (perfectOpenNested j).coarse ≫
        perfectOpenScalarZeroToCone j r q hq =
      perfectScalarInclusionNat X r ≫ perfectScalarConeProjectionNat X r := by
  apply NatTrans.ext
  funext K
  exact ((perfectOpenScalarCofibrationSequence j r).cofiber K).w.symm

/-- Weakness is exactly the preexisting acyclicity witness on the actual cone object. -/
theorem perfectOpenScalarZeroToCone_weak (K : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (perfectOpenNested j).coarse.weq ((perfectOpenScalarZeroToCone j r q hq).app K) :=
  zeroToAcyclicInclusion_weak (perfectOpenNested j)
    ((perfectOpenScalarConeFunctor j r q hq).obj K)

include hq in
/-- The middle component is the original inclusion, coarse weak by the old scalar factorization. -/
theorem perfectScalarInclusionNat_openWeak (K : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (perfectOpenNested j).coarse.weq ((perfectScalarInclusionNat X r).app K) :=
  perfectScalarInclusion_openWeak r j q hq K

/-- The unchanged fine weak projection is carried to the same coarse weak structure. -/
theorem perfectScalarProjectionNat_openWeak (K : ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (perfectOpenNested j).coarse.weq ((perfectScalarProjectionNat X r).app K) :=
  (perfectOpenNested j).le_weq _ (perfectScalarProjectionNat_weak X r K)

end AlgebraicGeometry.Scheme.Modules
