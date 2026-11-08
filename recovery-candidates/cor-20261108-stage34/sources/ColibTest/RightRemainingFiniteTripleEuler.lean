/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTripleEuler

/-! Literal endpoint consumers. Source-only; no compilation or kernel check performed. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingTheory.Sequence
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] Ideal.Quotient.field

namespace Stacks.Chow

section ResidueDegree

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i) [IsSeparated i]
  (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)

example
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : MaximalSpectrum (correspondenceRightRemainingFiniteRing f g h i z w v x)) :
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
    letI := moduleFinite_correspondenceRightRemainingFiniteRing f g h i z w v hw hv x
    Module.finiteAlgebraResidueDegree (correspondenceRightRemainingImageStalk f g h i z w v x)
      (correspondenceRightRemainingFiniteRing f g h i z w v x) q =
      Stacks.Length.primeResidueDegree
        (algebraMap (correspondenceRightRemainingImageStalk f g h i z w v x)
          (correspondenceRightRemainingFiniteRing f g h i z w v x))
        (q.asIdeal.comap (algebraMap (correspondenceRightRemainingImageStalk f g h i z w v x)
          (correspondenceRightRemainingFiniteRing f g h i z w v x))) q.asIdeal := by
  exact finiteAlgebraResidueDegree_correspondenceRightRemainingFiniteRing_eq_prime
    f g h i z w v hw hv x q

end ResidueDegree

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i]
  [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (hv : IsFiniteCorrespondencePoint h i v)

include hz hw hv

example
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v))
    {r : ℕ} (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)))
    (hsr : IsRegular ((pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1))) (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) :
    let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
    letI := isFinite_correspondenceTripleToRightImageIncidence f g h i z w v hw hv
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * Koszul.seqEuler (fun j => α (s j))
      ((ModuleCat.restrictScalars (algebraMap R B)).obj (M n))) =
      finiteCyclePushforward (correspondenceTripleToRightImageIncidence f g h i z w v)
        (correspondenceTripleIncidenceTorCycle K f g h i z w v hw hv) x.1 := by
  exact finsum_signed_correspondenceRightRemainingFiniteTorEuler_eq_tripleTorPushforward
    K f g h i z w v hz hw hv x s hsr hs

end Stacks.Chow
