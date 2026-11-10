/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpen
public import Colib.AlgebraicGeometry.Modules.PerfectOpenExtension
public import Colib.KTheory.Waldhausen.Fibration.LongExactSequence

/-!
# The actual bounded-flat relative-open fibration

Exact restriction proves extension for the original coarse weak class. The existing
identity-cone cylinder discharges the second-endpoint condition, without compactness
of either scheme or a supplied fiber comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Fibration AlgebraicGeometry.RingedSpace Topology

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Exact restriction proves extension for the actual coarse weak equivalences. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/OpenFibration.lean:37-42"
  "adaptation" "The coarse extension property from actual open restriction"]
theorem boundedAboveFlatPerfectOpenWaldhausen_extensionAxiom :
    ExtensionAxiom (boundedAboveFlatPerfectOpenWaldhausen j) :=
  Structure.withInverseImageWeak_extensionAxiom
    ((boundedAboveFlatPerfectInclusion_isExact X.toRingedSpace).comp
      (perfectComplexesRestrictOpenImmersion_isExact j))
    (perfectComplexes_extensionAxiom U.toRingedSpace)

/-- The original identity-cone second endpoint is a section of its projection. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/OpenFibration.lean:44-50"
  "adaptation" "The original second cylinder endpoint and projection"]
theorem boundedAboveFlatPerfectOpenJointData_secondEndpointSection :
    RowFactorization.SecondEndpointSection (boundedAboveFlatPerfectOpenNested j)
      (boundedAboveFlatPerfectOpenJointData j) :=
  boundedAboveFlatPerfectJointData_secondEndpointSection X.toRingedSpace
    (boundedAboveFlatPerfectOpenNested j)

/-- The canonical coarse-fiber comparison is weak with all premises discharged. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/OpenFibration.lean:52-57"
  "adaptation" "The original bounded-flat canonical fiber comparison without compactness"]
theorem boundedAboveFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (canonicalFiberMap (boundedAboveFlatPerfectOpenNested j)) :=
  canonicalFiberMap_isWeakHomotopyEquivalence_general (boundedAboveFlatPerfectOpenNested j)
    (boundedAboveFlatPerfectOpenWaldhausen_extensionAxiom j)
    (boundedAboveFlatPerfectOpenJointData j)
    (boundedAboveFlatPerfectOpenJointData_secondEndpointSection j)

end AlgebraicGeometry.Scheme.Modules
