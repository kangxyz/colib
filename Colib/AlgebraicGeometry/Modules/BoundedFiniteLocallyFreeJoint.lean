/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFiniteLocallyFreeWaldhausen
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.ComplexRelativeJoint

/-!
# Actual joint cylinders on bounded vector-bundle complexes

Native term boundedness, local finite freeness, and actual cone closure supply the original
joint cylinder. The fine weak class consists of quasi-isomorphisms. Its actual projection and
second endpoint retain the original section equation, for every nested coarse weak class.

Implementation provenance: `Quillen/AlgebraicGeometry/PerfectComplexes/StrictJointData.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

variable (X : Scheme.{u})

/-- The actual signed identity-cone cylinder with genuine quasi-isomorphism fine maps. -/
@[colib_tag "COL-0313",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/StrictJointData.lean:33-46"
    "adaptation" "Original strict joint cylinder, generalized to every nested weak class"]
def boundedFiniteLocallyFreeJointData
    (N : Waldhausen.Fibration.NestedWeakEquivalences (boundedFiniteLocallyFreeWaldhausen X)) :
    Waldhausen.Fibration.RowFactorization.JointData N :=
  Waldhausen.Fibration.complexJointDataOfNested (boundedFiniteLocallyFreeComplex X)
    boundedFiniteLocallyFreeComplex_mappingCone
    (fun _ h => boundedFiniteLocallyFreeComplex_shift h 1) N

/-- The original target endpoint is a section of the original cylinder projection. -/
theorem boundedFiniteLocallyFreeJointData_secondEndpointSection
    (N : Waldhausen.Fibration.NestedWeakEquivalences (boundedFiniteLocallyFreeWaldhausen X)) :
    Waldhausen.Fibration.RowFactorization.SecondEndpointSection N
      (boundedFiniteLocallyFreeJointData X N) :=
  Waldhausen.Fibration.complexJointDataOfNested_secondEndpointSection
    (boundedFiniteLocallyFreeComplex X) boundedFiniteLocallyFreeComplex_mappingCone
    (fun _ h => boundedFiniteLocallyFreeComplex_shift h 1) N

end Stacks.Perfect.BoundedLocallyFreeComplexes
