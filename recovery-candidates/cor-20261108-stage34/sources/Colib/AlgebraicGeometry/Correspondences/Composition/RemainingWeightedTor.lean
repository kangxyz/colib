/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingWeightedEuler
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingPrimeTorComparison

/-!
# Weighted remaining Tor at every original exterior label

The quotient Euler factors in the actual whole-family formula are now replaced
by the full signed native Tor coefficients against the actual remaining ambient
diagonal. The coefficient module is the actual prime-closure stalk quotient,
whose defining ideal is proved in `RemainingPrimeTorComparison`. The prime is
the literal contraction of the same original finite-algebra generic label.

Every summand retains the original pair Tor coefficient, full exterior fibre
length, and original exterior finite-map residue degree. The two homological
indices are independent and retain all signs. Neither an unknown comparison
nor vanishing of unwanted terms is assumed. Regrouping exterior labels by the
original pair image and upgrading the local identity to global cycles remains
outside this local weighted Tor statement.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (h : Z ⟶ Spec (.of k)) (i : W ⟶ Spec (.of k))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [IsSeparated g] [IsSeparated h]
  [IsLocallyNoetherian (correspondenceLeftIntermediateImageProduct f g h i z w v)]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (x : genericPoints (correspondenceLeftImageIncidence f g h i z w v))

local notation3 (prettyPrint := false) "R" =>
  correspondenceRemainingImageStalk f g h i z w v x.1
local notation3 (prettyPrint := false) "B" =>
  correspondenceRemainingFiniteRing f g h i z w v x.1
local notation3 (prettyPrint := false) "A" => (pullback h h).presheaf.stalk
  (correspondenceLeftImageMiddlePair f g h i z w v
    (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1))
local notation3 (prettyPrint := false) "α" =>
  correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1
local notation3 (prettyPrint := false) "M" =>
  correspondenceRemainingFiniteTorModule f g h i z w v x.1

include hz hw

/-- Actual remaining ambient Tor replaces every quotient Euler factor, while the original
source labels, original scheme residue weights, and full exterior fibre lengths are unchanged. -/
theorem finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_weightedTor {r : ℕ}
    (s : Fin r → A) (hr : RingTheory.Sequence.IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
    ∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
      Koszul.seqEuler (fun j => α (s j))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      ∑ᶠ η : correspondenceRemainingOriginalGenericLabels f g h i z w v x.1,
        let q := (correspondenceRemainingFiniteGenericEquivOriginal
          f g h i z w v x.1).symm η
        let p := (correspondenceRemainingFiniteGenericEquivMinPrime
          f g h i z w v hz hw x.1 q).1
        (correspondenceIncidenceTorCoefficient k f g h z w
          (correspondenceLeftExteriorGenericLabel f g h i z w v η.1) *
          (correspondenceLeftExteriorFiberLength f g h i z w v η.1.1 : ℤ)) *
          ((correspondenceLeftIntermediateImageMap f g h i z w v).residueDegree η.1.1 : ℤ) *
          (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
            ((Module.length (correspondenceRemainingAmbientStalk f g h i z w v x.1)
              (correspondenceRemainingImagePrimeTor f g h i z w v x.1 p n)).toNat : ℤ)) := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
  refine (finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_originalLabels
    k f g h i z w v hz hw x s hs).trans ?_
  apply finsum_congr
  intro η
  let e := correspondenceRemainingFiniteGenericEquivOriginal f g h i z w v x.1
  let q := e.symm η
  let p := (correspondenceRemainingFiniteGenericEquivMinPrime
    f g h i z w v hz hw x.1 q).1
  have hlabel : correspondenceRemainingFiniteGenericLabel
      f g h i z w v x.1 q = η.1 :=
    congrArg Subtype.val (e.apply_symm_apply η)
  have hpoint : correspondenceRemainingFiniteModelProjection
      f g h i z w v x.1 q.1 = η.1.1 :=
    congrArg Subtype.val hlabel
  have hdegree : Stacks.Length.primeResidueDegree (algebraMap R B)
      (p.asIdeal.comap (algebraMap R B)) p.asIdeal =
        (correspondenceLeftIntermediateImageMap f g h i z w v).residueDegree η.1.1 := by
    dsimp only [p]
    rw [correspondenceRemainingFiniteGenericEquivMinPrime_asIdeal f g h i z w v hz hw x.1 q,
      primeResidueDegree_correspondenceRemainingFiniteAlgebra f g h i z w v hz hw x.1 q.1,
      hpoint]
  dsimp only
  rw [hdegree]
  congr 1
  exact seqEuler_correspondenceRemainingImagePrime_eq_finsum_tor
    f g h i z w v x.1 p s hr hs

end Stacks.Chow
