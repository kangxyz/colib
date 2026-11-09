/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTorCoefficient
public import
  Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTorMinimalEuler

/-!
# Original-label Euler formula for the full finite Tor family

The all-degree integer Euler formula is reindexed along the proved actual
bijections from affine minimal primes to model generic points and then to the
retained original exterior generic points. Every split label is retained even
when several labels have the same image. The first coefficient is the original
pair Tor coefficient, multiplied by the full exterior fibre multiplicity.

The residue degree remains the native prime residue degree for the actual
finite algebra, at the literal affine prime of the model point. Its transport
to the original scheme residue degree is a separate comparison. Likewise, the
remaining factor is still the native quotient Koszul Euler characteristic;
identifying it with the image-component Tor factor is a separate endpoint.
No equality of the desired remaining cycles is a hypothesis of this formula.
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
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  [IsLocallyNoetherian (correspondenceRightIntermediateImageProduct f g h i z w v)]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) (hv :
    IsFiniteCorrespondencePoint h i v)

include hz

omit [IsLocallyNoetherian (correspondenceRightIntermediateImageProduct f g h i z w v)] in
/-- Model generic labels give the same actual Euler sum, with the original signed Tor
coefficient and the full exterior fibre factor in each summand. -/
theorem finsum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_genericPoints
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → ((pullback g g).presheaf.stalk
  (correspondenceRightImageMiddlePair f g h i z w v
    (correspondenceRightImageIncidenceInclusion f g h i z w v x.1))))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) :
    let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
    ∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
      Koszul.seqEuler (fun j => α (s j))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      ∑ᶠ q : genericPoints (correspondenceRightRemainingFiniteModel f g h i z w v x.1),
        let p := (correspondenceRightRemainingFiniteGenericEquivMinPrime
          f g h i z w v hw hv x.1 q).1
        (correspondenceIncidenceTorCoefficient k g h i w v
          (correspondenceRightExteriorGenericLabel f g h i z w v
            (correspondenceRightRemainingFiniteGenericLabel f g h i z w v x.1 q)) *
          (correspondenceRightExteriorFiberLength f g h i z w v
            (correspondenceRightRemainingFiniteModelProjection f g h i z w v x.1 q.1) : ℤ)) *
          (Stacks.Length.primeResidueDegree (algebraMap R B)
            (p.asIdeal.comap (algebraMap R B)) p.asIdeal : ℤ) *
          Koszul.seqEuler (fun j => α (s j)) (R ⧸ p.asIdeal.comap (algebraMap R B)) := by
  dsimp only
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
  refine (finsum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule
    k f g h i z w v hz hw hv x s hs).trans ?_
  symm
  apply finsum_eq_of_bijective
    (correspondenceRightRemainingFiniteGenericEquivMinPrime f g h i z w v hw hv x.1)
    (correspondenceRightRemainingFiniteGenericEquivMinPrime f g h i z w v hw hv x.1).bijective
  intro q
  dsimp only
  rw [finsum_signed_length_localized_correspondenceRightRemainingFiniteTorModule
    k f g h i z w v hw hv x.1 q]

omit [IsLocallyNoetherian (correspondenceRightIntermediateImageProduct f g h i z w v)] in
/-- All retained original exterior labels, including coincident-image labels, occur once.
The algebraic residue and quotient-Euler factors keep the literal corresponding source prime. -/
theorem finsum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_originalLabels
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → ((pullback g g).presheaf.stalk
  (correspondenceRightImageMiddlePair f g h i z w v
    (correspondenceRightImageIncidenceInclusion f g h i z w v x.1))))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) :
    let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
    ∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
      Koszul.seqEuler (fun j => α (s j))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      ∑ᶠ η : correspondenceRightRemainingOriginalGenericLabels f g h i z w v x.1,
        let q := (correspondenceRightRemainingFiniteGenericEquivOriginal
          f g h i z w v x.1).symm η
        let p := (correspondenceRightRemainingFiniteGenericEquivMinPrime
          f g h i z w v hw hv x.1 q).1
        (correspondenceIncidenceTorCoefficient k g h i w v
          (correspondenceRightExteriorGenericLabel f g h i z w v η.1) *
          (correspondenceRightExteriorFiberLength f g h i z w v η.1.1 : ℤ)) *
          (Stacks.Length.primeResidueDegree (algebraMap R B)
            (p.asIdeal.comap (algebraMap R B)) p.asIdeal : ℤ) *
          Koszul.seqEuler (fun j => α (s j)) (R ⧸ p.asIdeal.comap (algebraMap R B)) := by
  dsimp only
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
  refine (finsum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_genericPoints
    k f g h i z w v hz hw hv x s hs).trans ?_
  symm
  let e := correspondenceRightRemainingFiniteGenericEquivOriginal f g h i z w v x.1
  apply finsum_eq_of_bijective e.symm e.symm.bijective
  intro η
  dsimp only
  have hlabel : correspondenceRightRemainingFiniteGenericLabel
      f g h i z w v x.1 (e.symm η) = η.1 :=
    congrArg Subtype.val (e.apply_symm_apply η)
  have hpoint : correspondenceRightRemainingFiniteModelProjection
      f g h i z w v x.1 (e.symm η).1 = η.1.1 :=
    congrArg Subtype.val hlabel
  rw [hlabel, hpoint]

end Stacks.Chow
