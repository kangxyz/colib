/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.AffineTorComparison
public import Colib.AlgebraicGeometry.Correspondences.Composition.AffinePulledStalks

/-!
# Actual affine middle-diagonal Tor length comparison

At each point of the actual correspondence incidence, the native Tor length over
its four-factor ambient stalk equals the native Tor length of the two original
pulled ideal subschemes over the actual triple-product stalk. The product support
is first on the ambient side; the left pulled support is first on the triple side.
Both potentially nonreduced support schemes and their actual stalk maps remain.

The proof constructs the adjacent quotient charts once and uses those same charts
for the ambient comparison and the two pulled-support module identifications.
There is no module/Tor comparison, flat support, finiteness or supplied chart among
the hypotheses. The degree is arbitrary and length takes values in `ℕ∞`.

Implementation source: `motivic_source_a6805c4`,
`Motivic/Aglib/AlgebraicGeometry/Intersection/AffineMiddleTor.lean`,
`stalkTor_length`, applied to the actual correspondence incidence geometry.
Mathematical context: Stacks Project, Tags 0B0T, 00M8 and 00IX; MVW2006,
Lecture 1, composition of finite correspondences. The statement here is the affine
all-degree local length comparison. Neighborhood globalization, finite Euler sums,
Tor cycles, weighted pushforward, units and associativity are separate obligations.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Algebra.TensorProduct.MiddleDiagonal
open scoped TensorProduct

universe u

namespace Stacks.Chow

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

local instance affineActualTorAtPrimeRing {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    Ring (Localization.AtPrime p) := (inferInstance : CommRing (Localization.AtPrime p)).toRing

local notation "fA" => Spec.map (CommRingCat.ofHom (algebraMap k A))
local notation "fB" => Spec.map (CommRingCat.ofHom (algebraMap k B))
local notation "fC" => Spec.map (CommRingCat.ofHom (algebraMap k C))

/-- Actual four-factor ambient Tor and actual triple-product pulled-support Tor
have equal length at every incidence point and every degree over an arbitrary field.
All coordinate charts and comparisons are constructed; length may be infinite. -/
theorem affineIncidenceTor_length_eq_pulledStalkTor
    (z : pullback (C := Scheme) fA fB) (w : pullback (C := Scheme) fB fC)
    (t : correspondenceIncidence fA fB fC z w) (n : ℕ) :
      Module.length
        ((correspondenceIntersectionAmbient fA fB fC).presheaf.stalk
          (correspondenceIncidenceAmbientInclusion fA fB fC z w t))
        (((Tor (ModuleCat ((correspondenceIntersectionAmbient fA fB fC).presheaf.stalk
            (correspondenceIncidenceAmbientInclusion fA fB fC z w t))) n).obj
          (correspondenceIncidenceSupportStalkModule fA fB fC z w t)).obj
          (correspondenceIncidenceTripleStalkModule fA fB fC z w t)) =
      Module.length ((correspondenceTripleProduct fA fB fC).presheaf.stalk
        (correspondenceIncidenceInclusion fA fB fC z w t))
        (((Tor (ModuleCat ((correspondenceTripleProduct fA fB fC).presheaf.stalk
            (correspondenceIncidenceInclusion fA fB fC z w t))) n).obj
          (correspondenceIncidenceLeftPulledStalkModule fA fB fC z w t)).obj
          (correspondenceIncidenceRightPulledStalkModule fA fB fC z w t)) := by
  obtain ⟨I, J, eI, eJ, hI, hJ, eP, hP⟩ :=
    exists_correspondenceAffineSupportProductCoordinates k A B C z w
  exact (affineIncidenceTor_length_eq_middleSupportTor_of_supportProductChart
    k A B C z w I J eP hP t n).trans
      (affinePulledStalkTor_length_eq_middleSupportTor k A B C z w I J eI eJ hI hJ t n).symm

end Stacks.Chow
