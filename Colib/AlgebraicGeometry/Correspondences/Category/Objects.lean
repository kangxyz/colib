/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Basic

/-!
# Objects of the category of finite correspondences

`Cor k` wraps the existing smooth separated finite-type site object, so that its eventual
finite-correspondence category structure does not replace the ordinary smooth-site category.
The underlying scheme and structure morphism are the existing native objects. No new
scheme, support, cycle, composition operation, or category law is introduced here.

The quasi-compact structure map to `Spec k` gives compactness of the source. This is the
finiteness needed later for the full componentwise identity graph, including disconnected
and empty schemes over an arbitrary field.

Implementation provenance: `motivic_source_a6805c4`,
`Motivic/AlgebraicGeometry/Correspondences/Basic.lean`, blob
`f09b33fa79079e5ffa6f4772563f3d27f4085e4f`, the `Cor` object wrapper.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Smooth separated finite-type schemes, with a distinct object type for finite correspondences.
The ordinary scheme and all its geometric data remain the existing smooth-site object. -/
structure Cor (k : Type u) [Field k] : Type (u + 1) where
  /-- The actual underlying smooth separated finite-type object. -/
  toSmoothSite : Scheme.SmoothSite (Spec (.of k))

namespace Cor

variable {k : Type u} [Field k]

/-- Finite type over the affine point supplies compactness, not an extra condition on objects. -/
instance (X : Cor k) : CompactSpace X.toSmoothSite.left :=
  QuasiCompact.compactSpace_of_compactSpace (Y := Spec (.of k)) X.toSmoothSite.hom

end Cor

end AlgebraicGeometry
