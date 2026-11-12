/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Basic

/-!
# Smooth affine schemes and algebra maps

The spectrum of a smooth algebra is an object of the actual smooth site.
The morphism associated to an algebra map is its literal spectrum map.

Extracted from `Motivic/Aglib/AlgebraicGeometry/Spec/PolynomialQuotient/ScalarMap.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`, blob
`7653510d0ce4597e41983335434a511fa9dd33de`.
No polynomial quotient or Laurent construction is needed for this interface.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

/-- The structural spectrum map of an algebra. -/
abbrev affineBaseMap (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] :
    Spec (.of R) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k R))

variable {k R S : Type u} [Field k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra.Smooth k R]

instance affineBaseMap_smooth : Smooth (affineBaseMap k R) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)

/-- A smooth algebra with its original structural map. -/
def affineSite (k R : Type u) [Field k] [CommRing R]
    [Algebra k R] [Algebra.Smooth k R] : SmoothSite (Spec (.of k)) :=
  mk (affineBaseMap k R)

/-- Any algebra map induces its actual smooth-site morphism. -/
def affineMorphism [Algebra.Smooth k S] (φ : R →ₐ[k] S) :
    affineSite k S ⟶ affineSite k R :=
  homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact φ.commutes r)

end AlgebraicGeometry.Scheme.SmoothSite
