/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Generalizing.GenericPoints
public import Mathlib.AlgebraicGeometry.Noetherian
public import Colib.AlgebraicGeometry.Morphisms.QuasiFinite.GenericFiber

/-!
# Actual fibers above generic points

A locally quasi-finite scheme map reflects generic points: a point mapping to
an actual generic point has no strict generization, because its fiber is
discrete. This gives a literal reindexing of that fiber by source generic
points. No dimension, purity, integrality or reducedness assumption is used.
The converse direction needs a genuine generalizing-map hypothesis; finite
maps alone need not send every source generic point to a target generic point.
-/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Morphisms/QuasiFinite/GenericFiber.lean`, blob
`d1085d9cc5ef7fcecf30149a6c0ad58fd1f0480a`.
The source is the actual original scheme or ordinary free-Yoneda Ext group.
All monic quotient fibers retain their full scheme structure.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]

/-- With genuine generalization lifting, the generic-point criterion is bidirectional. -/
theorem image_mem_genericPoints_iff_of_generalizing (hf : GeneralizingMap f) (x : X) :
    f x ∈ genericPoints Y ↔ x ∈ genericPoints X :=
  ⟨mem_genericPoints_of_image_generic f x, mem_genericPoints_of_generalizing f hf x⟩

end AlgebraicGeometry.Scheme.Hom
