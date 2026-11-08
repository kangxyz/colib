/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectOpenExtension
public import Colib.AlgebraicGeometry.Modules.PerfectOpenJoint
public import Colib.KTheory.Waldhausen.Fibration.GeneralComparison

/-!
# The actual relative-open fiber theorem on native perfect complexes

The native ambient-monomorphism joint cylinder supplies the structural hypotheses of
Waldhausen's fiber theorem. The canonical comparison map, with its original nullhomotopy,
is unchanged. The target is the relative coarse structure, not fine K-theory of the open.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/OpenFibration.lean:97-117`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. The native Mono joint cylinder
replaces the old exact-subcategory admissibility argument.
-/

@[expose] public noncomputable section

open CategoryTheory Topology

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- The original canonical relative-coarse fiber map is a full weak homotopy equivalence. -/
@[colib_tag "COL-0300",
  colib_ref "Waldhausen1985" "Section 1.6, Theorem 1.6.4 and proof, pp. 350-352"
    "adaptation"
    "Native perfect complexes with open-detected weak equivalences and the actual joint cylinder"]
theorem perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    IsWeakHomotopyEquivalence (Waldhausen.Fibration.canonicalFiberMap (perfectOpenNested j)) :=
  Waldhausen.Fibration.canonicalFiberMap_isWeakHomotopyEquivalence_general
    (perfectOpenNested j) (perfectOpenWeak_extensionAxiom j)
    (perfectOpenJointData j) (perfectOpenJointData_secondEndpointSection j)

end AlgebraicGeometry.Scheme.Modules
