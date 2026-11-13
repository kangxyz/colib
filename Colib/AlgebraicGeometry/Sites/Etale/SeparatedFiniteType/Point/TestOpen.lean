/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.CompositionObjects
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.OpenObjects


/-! # Persistent section detection on arbitrary original small-site test objects -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
https://github.com/kangxyz/motivic/blob/a6805c4a87cdfd7717dd7a94039246a167f15380/Motivic/Aglib/AlgebraicGeometry/Sites/Etale/SeparatedFiniteType/Point/Persistent/MarkedSection.lean
Source blob `9f8ff5275051ed22d1d81ac4845c70273acfaf91`.
Only original testOpenObject and testOpenInclusion are extracted; composition objects are the
frozen batch02 declarations.
Source candidate only; no elaboration result is asserted.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {S : Scheme.{u}}

/-- The original open part of V, still an object over the unchanged site base S. -/
def testOpenObject (V : EtaleSeparatedFiniteType S) [IsNoetherian V.left] (O : V.left.Opens) :
    EtaleSeparatedFiniteType S := composeObject V (openObject O)

/-- The literal inclusion of the original open test object into `V`. -/
def testOpenInclusion (V : EtaleSeparatedFiniteType S) [IsNoetherian V.left] (O : V.left.Opens) :
    testOpenObject V O ⟶ V := composeObjectProjection V (openObject O)


end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
