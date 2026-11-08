/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectScalarCofiber
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenSupport
public import Colib.KTheory.Waldhausen.GrothendieckComparison.ObjectNaturality

/-! # Canonical K-maps of the native supported scalar cone

These are the genuine same-degree maps of the original exact scalar-cone
functors. The degree-zero equations retain the literal signed cone and the
quotient-preserving categorical-cofiber comparison. No connecting boundary is
identified here.

Adapted from Quillen/AlgebraicGeometry/PerfectComplexes/ScalarConeFunctor.lean:90-104
and ScalarCofiber.lean:71-78 at c561118b7795eb9780be9ed391c3251d6a4d0afd.
-/

@[expose] public noncomputable section
open CategoryTheory Waldhausen Fibration
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The actual scalar-cone functor's same-degree K-map into the supported category. -/
def perfectSupportedScalarConeKMap (n : ℕ) :
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K n →* PerfectSupportedK j n :=
  KMap (perfectSupportedScalarConeFunctor_waldhausenExact j r q hq) n

/-- The same canonical map into the original relative-acyclic category. -/
def perfectOpenScalarConeKMap (n : ℕ) :
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K n →*
      (acyclicStructure (perfectOpenNested j)).K n :=
  KMap (perfectOpenScalarConeFunctor_waldhausenExact j r q hq) n

/-- Degree-zero evaluation keeps the original signed cone object. -/
theorem perfectOpenScalarConeKMap_objectClass
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    perfectOpenScalarConeKMap j r q hq 0
        ((RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).kZeroObjectClass K) =
      (acyclicStructure (perfectOpenNested j)).kZeroObjectClass
        (perfectOpenScalarCone r j q hq K) :=
  KMap_kZeroObjectClass (perfectOpenScalarConeFunctor_waldhausenExact j r q hq) K

/-- The original categorical cofiber and signed cone have the same relative-acyclic class. -/
theorem perfectOpenScalarCofiberAcyclic_class
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (acyclicStructure (perfectOpenNested j)).kZeroObjectClass
        (perfectOpenScalarCofiberAcyclic r j q hq K) =
      (acyclicStructure (perfectOpenNested j)).kZeroObjectClass
        (perfectOpenScalarCone r j q hq K) :=
  (acyclicStructure (perfectOpenNested j)).kZeroObjectClass_iso
    (perfectOpenScalarCofiberAcyclicIso r j q hq K)

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarConeFunctor.lean:90-104"
  "adaptation" "The same-degree canonical K-maps and their original signed cone object class"]
  AlgebraicGeometry.Scheme.Modules.perfectSupportedScalarConeKMap
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarConeKMap
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarConeKMap_objectClass
