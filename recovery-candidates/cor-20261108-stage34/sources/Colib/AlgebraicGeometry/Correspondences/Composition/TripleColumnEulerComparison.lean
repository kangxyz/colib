/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleLeftColumnEuler
public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleRightColumnTor

/-!
# The genuine left and right first-stage column Euler coefficients agree

At an original generic triple-incidence label, native local triple-Tor
associativity equates the two full signed iterated coefficients. The proved
left and right scalar/Koszul comparisons identify those coefficients with the
literal finite column Euler sums over the two actual first-stage local rings.
Neither sum is an abstract witness or a fundamental-cycle replacement. All
individual lengths are finite by the actual generic-support criterion, and
all degrees outside the stated list bounds vanish by the regular resolutions.

The field is arbitrary and the ambient schemes may be disconnected. This is
local coefficient equality on the existing triple support, not yet either
global correspondence bracket or an equality of total-homology Euler sums.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence TopologicalSpace
open scoped BigOperators

universe u

namespace Stacks.Chow

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (h : Z ⟶ Spec (.of k)) (i : W ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : genericPoints (correspondenceTripleIncidence f g h i z w v))

local notation3 (prettyPrint := false) "A" =>
  correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
local notation3 (prettyPrint := false) "φ" =>
  correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x.1
local notation3 (prettyPrint := false) "κ" =>
  correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x.1
local notation3 (prettyPrint := false) "p" =>
  correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
local notation3 (prettyPrint := false) "IY" =>
  IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p
local notation3 (prettyPrint := false) "IZ" =>
  IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p

/-- Equality of the actual full signed column coefficients in their two genuine
first-stage local rings, at a fixed original generic triple-incidence point. -/
theorem sum_signed_correspondenceTripleIncidence_columnEuler_eq
    (t s : List A) (ht : IsRegular A t) (hs : IsRegular A s)
    (hY : IY = Ideal.ofList t) (hZ : IZ = Ideal.ofList s) :
    (∑ b : Fin (t.length + 1), (-1 : ℤ) ^ (b : ℕ) *
      Koszul.seqEuler (fun j => φ (s.get j))
        (correspondenceRemainingFirstKoszulModule f g h i z w v x.1 t ht hY b)) =
    ∑ b : Fin (s.length + 1), (-1 : ℤ) ^ (b : ℕ) *
      Koszul.seqEuler (fun j => κ (t.get j))
        (correspondenceRightRemainingFirstKoszulModule f g h i z w v x.1 s hs hZ b) :=
  (finsum_signed_leftIteratedTor_eq_sum_remainingFirstEuler
    f g h i z w v x.1 t s ht hs hY hZ).symm.trans
      ((finsum_signed_length_correspondenceTripleIncidence_iteratedTor_eq
        k f g h i z w v x).trans
        (finsum_signed_rightIteratedTor_eq_sum_remainingFirstEuler
          f g h i z w v x.1 t s ht hs hY hZ))

end Stacks.Chow
