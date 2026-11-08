/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectGlobalScalar
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenSupport
public import Colib.KTheory.Waldhausen.AutomorphismKOne

/-! # Independent forward scalar classes on native perfect complexes

The class is defined from the actual scalar arrow and its weak-arrow square, before any
cofiber or connecting-map construction. Normalization is the existing inverse-prefix
normalization on the original object-loop component.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberPasting.lean:69-73`
and `ScalarCofiberKOneNormalization.lean:135-136` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
open CategoryTheory Waldhausen Fibration Topology
open scoped Topology
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The original forward scalar square at the actual object-loop component. -/
def perfectScalarWeakLoop :
    Path ((perfectOpenNested j).coarse.kZeroObjectLoop K)
      ((perfectOpenNested j).coarse.kZeroObjectLoop K) :=
  (perfectOpenNested j).coarse.weakObjectSquareLoopPath ((perfectGlobalScalar X r).app K)
    (quasiIso_restrict_complexGlobalScalar j r q hq K.obj)

/-- The independent class of the forward scalar, with no boundary or fiber input. -/
def perfectScalarForwardKOneClass : PerfectOpenK j 1 :=
  (perfectOpenNested j).coarse.weakEndomorphismKOneClass ((perfectGlobalScalar X r).app K)
    (quasiIso_restrict_complexGlobalScalar j r q hq K.obj)

/-- The independent class retains the whole original weak-arrow loop. -/
theorem perfectScalarForwardKOneClass_eq :
    perfectScalarForwardKOneClass j K r q hq =
      loopKOneNormalization ((perfectOpenNested j).coarse.kZeroObjectLoop K)
        (FundamentalGroup.fromPath ⟦perfectScalarWeakLoop j K r q hq⟧) := rfl

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberKOneNormalization.lean:135-136"
    "adaptation"
  "The forward scalar weak-arrow class is defined independently of any boundary or fiber input; the
    existing generic inverse-prefix normalization is retained"]
  perfectScalarForwardKOneClass

attribute [colib_tag "COL-0304"] perfectScalarForwardKOneClass

end AlgebraicGeometry.Scheme.Modules
