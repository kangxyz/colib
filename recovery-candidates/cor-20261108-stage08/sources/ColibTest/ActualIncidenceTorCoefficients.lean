/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.PulledTorCoefficients
import Colib.AlgebraicGeometry.Sites.Smooth.Basic

/-! Source-only client tests. These have not been run or attributed a historical PASS. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open scoped BigOperators

universe u

namespace ColibTest.ActualIncidenceTorCoefficients

section GeneralBase

variable {S X Y Z : Scheme.{u}} [IsLocallyNoetherian S]
variable (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
variable [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType h] [IsSeparated g]
variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

-- No regularity, flatness, integrality, connectedness, or comparison hypotheses.
example (t : genericPoints (correspondenceIncidence f g h z w)) (n : ℕ) :
    Module.length ((correspondenceIntersectionAmbient f g h).presheaf.stalk
      (correspondenceIncidenceAmbientInclusion f g h z w t.val))
      (((Tor (ModuleCat ((correspondenceIntersectionAmbient f g h).presheaf.stalk
        (correspondenceIncidenceAmbientInclusion f g h z w t.val))) n).obj
        (correspondenceIncidenceSupportStalkModule f g h z w t.val)).obj
        (correspondenceIncidenceTripleStalkModule f g h z w t.val)) ≠ ⊤ :=
  correspondenceIncidenceTor_length_ne_top f g h z w t n

example (t : genericPoints (correspondenceIncidence f g h z w)) (n : ℕ) :
    IsFiniteLength ((correspondenceIntersectionAmbient f g h).presheaf.stalk
      (correspondenceIncidenceAmbientInclusion f g h z w t.val))
      (correspondenceIncidenceTor f g h z w t.val n) :=
  Module.length_ne_top_iff.mp (correspondenceIncidenceTor_length_ne_top f g h z w t n)

end GeneralBase

section SmoothSite

variable (k : Type u) [Field k]
variable (X Y Z : Scheme.SmoothSite (Spec (.of k)))
variable (z : pullback (C := Scheme) X.hom Y.hom) (w : pullback (C := Scheme) Y.hom Z.hom)

-- Native SmoothSite, arbitrary field, no irreducibility/nonemptiness hypotheses.
example (t : correspondenceIncidence X.hom Y.hom Z.hom z w) (n : ℕ)
    (hn : correspondenceIncidenceTorDegreeBound k X.hom Y.hom Z.hom z w t < n) :
    IsZero (correspondenceIncidenceTor X.hom Y.hom Z.hom z w t n) :=
  isZero_correspondenceIncidenceTor_of_lt k X.hom Y.hom Z.hom z w t n hn

example (t : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w)) (n : ℕ) :
    ((Module.length ((correspondenceIntersectionAmbient X.hom Y.hom Z.hom).presheaf.stalk
        (correspondenceIncidenceAmbientInclusion X.hom Y.hom Z.hom z w t.val))
      (correspondenceIncidenceTor X.hom Y.hom Z.hom z w t.val n)).toNat : ℕ∞) =
      Module.length ((correspondenceIntersectionAmbient X.hom Y.hom Z.hom).presheaf.stalk
        (correspondenceIncidenceAmbientInclusion X.hom Y.hom Z.hom z w t.val))
        (correspondenceIncidenceTor X.hom Y.hom Z.hom z w t.val n) :=
  natCast_toNat_length_correspondenceIncidenceTor X.hom Y.hom Z.hom z w t n

example (t : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w)) :
    (Function.support
      (correspondenceIncidenceTorTerm k X.hom Y.hom Z.hom z w t)).Finite :=
  finite_support_correspondenceIncidenceTorTerm k X.hom Y.hom Z.hom z w t

example (t : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w)) :
    correspondenceIncidenceTorCoefficient k X.hom Y.hom Z.hom z w t =
      ∑ n ∈ Finset.range
        (correspondenceIncidenceTorDegreeBound k X.hom Y.hom Z.hom z w t.val + 1),
        correspondenceIncidenceTorTerm k X.hom Y.hom Z.hom z w t n :=
  correspondenceIncidenceTorCoefficient_eq_sum_range k X.hom Y.hom Z.hom z w t _ le_rfl

example (t : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w)) (n : ℕ) :
    Module.length ((correspondenceTripleProduct X.hom Y.hom Z.hom).presheaf.stalk
      (correspondenceIncidenceInclusion X.hom Y.hom Z.hom z w t.val))
      (((Tor (ModuleCat ((correspondenceTripleProduct X.hom Y.hom Z.hom).presheaf.stalk
        (correspondenceIncidenceInclusion X.hom Y.hom Z.hom z w t.val))) n).obj
        (correspondenceIncidenceLeftPulledStalkModule X.hom Y.hom Z.hom z w t.val)).obj
        (correspondenceIncidenceRightPulledStalkModule X.hom Y.hom Z.hom z w t.val)) ≠ ⊤ :=
  pulledStalkTor_length_ne_top k X.hom Y.hom Z.hom z w t n

-- Empty incidence is permitted; no generic point is silently selected.
example [IsEmpty (correspondenceIncidence X.hom Y.hom Z.hom z w)] :
    ∀ t : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w),
      correspondenceIncidenceTorCoefficient k X.hom Y.hom Z.hom z w t = 0 :=
  fun t ↦ isEmptyElim t.val

end SmoothSite

end ColibTest.ActualIncidenceTorCoefficients
