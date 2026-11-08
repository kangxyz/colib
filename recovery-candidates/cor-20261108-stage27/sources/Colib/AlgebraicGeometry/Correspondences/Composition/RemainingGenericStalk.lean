/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleAmbient
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Support
public import StacksFrontier.RingTheory.HilbertSamuel.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Artinian.Ring

/-!
# The actual remaining diagonal is an ideal of definition at a generic intersection

The local ring is that of the full first-stage incidence times the third
support, at the image of an original generic triple-incidence point. The ideal
is the kernel of the actual remaining-diagonal stalk map. Its quotient is the
full triple-incidence stalk, not its reduction. The native generic-stalk
Artinian theorem proves that this quotient is Artinian and that the remaining
ideal is an ideal of definition. Neither fact is a caller-supplied substitute.

This supplies the geometric finite-colength input for native Koszul Euler
dévissage. It does not identify the first-stage Tor homology modules or assert
the weighted remaining-cycle comparison.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The actual full first-stage exterior local ring at a triple-incidence point. -/
abbrev correspondenceRemainingOriginalStalk
    (x : correspondenceTripleIncidence f g h i z w v) :=
  (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk
    (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x)

/-- The literal remaining-diagonal kernel in the full first-stage exterior local ring. -/
abbrev correspondenceRemainingOriginalStalkIdeal
    (x : correspondenceTripleIncidence f g h i z w v) :
    Ideal (correspondenceRemainingOriginalStalk f g h i z w v x) :=
  RingHom.ker
    ((correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v).stalkMap x).hom

/-- The actual remaining quotient is the full triple-incidence local ring. -/
def correspondenceRemainingOriginalStalkQuotientEquiv [IsSeparated h]
    (x : correspondenceTripleIncidence f g h i z w v) :
    (correspondenceRemainingOriginalStalk f g h i z w v x ⧸
      correspondenceRemainingOriginalStalkIdeal f g h i z w v x) ≃+*
        (correspondenceTripleIncidence f g h i z w v).presheaf.stalk x :=
  RingHom.quotientKerEquivOfSurjective
    (f := ((correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v).stalkMap x).hom)
    (SurjectiveOnStalks.stalkMap_surjective
      (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v) x)

/-- The quotient map is the original remaining-diagonal stalk map on every germ. -/
@[simp]
theorem correspondenceRemainingOriginalStalkQuotientEquiv_mk [IsSeparated h]
    (x : correspondenceTripleIncidence f g h i z w v)
    (a : correspondenceRemainingOriginalStalk f g h i z w v x) :
    correspondenceRemainingOriginalStalkQuotientEquiv f g h i z w v x
      (Ideal.Quotient.mk (correspondenceRemainingOriginalStalkIdeal f g h i z w v x) a) =
        ((correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v).stalkMap x).hom a := by
  simp [correspondenceRemainingOriginalStalkQuotientEquiv]

/-- The actual remaining quotient is Artinian at every original generic
triple-incidence label, including nilpotents. -/
theorem isArtinianRing_correspondenceRemainingOriginalStalkQuotient [IsSeparated h]
    [IsLocallyNoetherian (correspondenceLeftIntermediateSupportProduct f g h i z w v)]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    IsArtinianRing (correspondenceRemainingOriginalStalk f g h i z w v x.1 ⧸
      correspondenceRemainingOriginalStalkIdeal f g h i z w v x.1) := by
  let := LocallyOfFiniteType.isLocallyNoetherian
    (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v)
  let := generic_stalk_artinian x
  exact RingEquiv.isArtinianRing
    (correspondenceRemainingOriginalStalkQuotientEquiv f g h i z w v x.1).symm

/-- The finite-colength hypothesis for Euler dévissage is proved from the
actual generic remaining intersection and the actual local stalk map. -/
theorem isIdealOfDefinition_correspondenceRemainingOriginalStalkIdeal [IsSeparated h]
    [IsLocallyNoetherian (correspondenceLeftIntermediateSupportProduct f g h i z w v)]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    IsIdealOfDefinition (correspondenceRemainingOriginalStalkIdeal f g h i z w v x.1) := by
  let := LocallyOfFiniteType.isLocallyNoetherian
    (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v)
  let := generic_stalk_artinian x
  change Ideal.radical (RingHom.ker
    ((correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v).stalkMap x.1).hom) = _
  rw [RingHom.ker_eq_comap_bot, ← Ideal.comap_radical,
    ← IsArtinianRing.jacobson_eq_radical, IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top,
    IsLocalRing.maximalIdeal_comap]

end Stacks.Chow
