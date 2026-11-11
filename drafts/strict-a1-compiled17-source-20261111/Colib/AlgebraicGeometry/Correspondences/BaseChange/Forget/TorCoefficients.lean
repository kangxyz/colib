/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.BaseChange.Forget.IncidenceTor
public import Colib.AlgebraicGeometry.Correspondences.Composition.ActualTorCoefficients
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent

/-!
# Native signed Tor coefficients after forgetting an unramified field base

The original whole-incidence isomorphism transports every generic point. The
actual ambient Tor lengths agree in every degree by the two open squares.
Taking the same signed terms and native `finsum` therefore preserves the actual
coefficient, without a cutoff comparison or a geometric-integrality assumption.

Adapted from motivic `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/BaseChange/Forget/IncidenceTor.lean`.
Generic points use the native Stacks `genericPointsIso` of the actual incidence
isomorphism, not a generic point chosen from a finite scalar fibre.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

section Generics

variable {S T X Y Z : Scheme.{u}} (r : T ⟶ S)
  (f : X ⟶ T) (g : Y ⟶ T) (h : Z ⟶ T) [IsSeparated r]
  (z : pullback f g) (w : pullback g h)

/-- The actual whole-incidence isomorphism transports all native generic points. -/
def forgetBaseIncidenceGenericsEquiv :
    genericPoints (correspondenceIncidence f g h z w) ≃
      genericPoints (correspondenceIncidence (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w)) :=
  genericPointsIso (forgetBaseIncidenceIso r f g h z w)

/-- The transported generic point is the image under the actual incidence map. -/
@[simp]
theorem forgetBaseIncidenceGenericsEquiv_apply
    (t : genericPoints (correspondenceIncidence f g h z w)) :
    (forgetBaseIncidenceGenericsEquiv r f g h z w t).val =
      forgetBaseIncidenceMap r f g h z w t.val := rfl

end Generics

variable {k L : Type u} [Field k] [Field L]
  {X Y Z : Scheme.{u}} (r : Spec (.of L) ⟶ Spec (.of k))
  (f : X ⟶ Spec (.of L)) (g : Y ⟶ Spec (.of L)) (h : Z ⟶ Spec (.of L))
  [IsSeparated r] [FormallyUnramified r] [LocallyOfFiniteType r]
  (z : pullback f g) (w : pullback g h)

/-- The sign and each actual Tor length are unchanged, degree by degree. -/
theorem forgetBase_correspondenceIncidenceTorTerm
    (t : genericPoints (correspondenceIncidence f g h z w)) (n : ℕ) :
    correspondenceIncidenceTorTerm k (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w)
        (forgetBaseIncidenceGenericsEquiv r f g h z w t) n =
      correspondenceIncidenceTorTerm L f g h z w t n := by
  unfold correspondenceIncidenceTorTerm
  rw [forgetBaseIncidenceGenericsEquiv_apply, forgetBaseIncidenceTor_length]

/-- The complete alternating integer coefficient is unchanged; no higher Tor term is lost. -/
theorem forgetBase_correspondenceIncidenceTorCoefficient
    (t : genericPoints (correspondenceIncidence f g h z w)) :
    correspondenceIncidenceTorCoefficient k (f ≫ r) (g ≫ r) (h ≫ r)
        (forgetBaseProductMap r f g z) (forgetBaseProductMap r g h w)
        (forgetBaseIncidenceGenericsEquiv r f g h z w t) =
      correspondenceIncidenceTorCoefficient L f g h z w t := by
  unfold correspondenceIncidenceTorCoefficient
  apply finsum_congr
  intro n
  exact forgetBase_correspondenceIncidenceTorTerm r f g h z w t n

end Stacks.Chow
