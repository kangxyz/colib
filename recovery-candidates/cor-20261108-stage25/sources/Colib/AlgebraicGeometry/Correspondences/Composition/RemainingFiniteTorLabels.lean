/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteTorCoefficient
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteTorEuler

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

/-- Model generic labels give the same actual Euler sum, with the original signed Tor
coefficient and the full exterior fibre factor in each summand. -/
theorem finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_genericPoints {r : ℕ}
    (s : Fin r → A)
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
    ∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
      Koszul.seqEuler (fun j => α (s j))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      ∑ᶠ q : genericPoints (correspondenceRemainingFiniteModel f g h i z w v x.1),
        let p := (correspondenceRemainingFiniteGenericEquivMinPrime
          f g h i z w v hz hw x.1 q).1
        (correspondenceIncidenceTorCoefficient k f g h z w
          (correspondenceLeftExteriorGenericLabel f g h i z w v
            (correspondenceRemainingFiniteGenericLabel f g h i z w v x.1 q)) *
          (correspondenceLeftExteriorFiberLength f g h i z w v
            (correspondenceRemainingFiniteModelProjection f g h i z w v x.1 q.1) : ℤ)) *
          (Stacks.Length.primeResidueDegree (algebraMap R B)
            (p.asIdeal.comap (algebraMap R B)) p.asIdeal : ℤ) *
          Koszul.seqEuler (fun j => α (s j)) (R ⧸ p.asIdeal.comap (algebraMap R B)) := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
  refine (finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule
    k f g h i z w v hz hw x s hs).trans ?_
  symm
  apply finsum_eq_of_bijective
    (correspondenceRemainingFiniteGenericEquivMinPrime f g h i z w v hz hw x.1)
    (correspondenceRemainingFiniteGenericEquivMinPrime f g h i z w v hz hw x.1).bijective
  intro q
  dsimp only
  rw [finsum_signed_length_localized_correspondenceRemainingFiniteTorModule
    k f g h i z w v hz hw x.1 q]

/-- All retained original exterior labels, including coincident-image labels, occur once.
The algebraic residue and quotient-Euler factors keep the literal corresponding source prime. -/
theorem finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_originalLabels {r : ℕ}
    (s : Fin r → A)
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
          (Stacks.Length.primeResidueDegree (algebraMap R B)
            (p.asIdeal.comap (algebraMap R B)) p.asIdeal : ℤ) *
          Koszul.seqEuler (fun j => α (s j)) (R ⧸ p.asIdeal.comap (algebraMap R B)) := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
  refine (finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_genericPoints
    k f g h i z w v hz hw x s hs).trans ?_
  symm
  let e := correspondenceRemainingFiniteGenericEquivOriginal f g h i z w v x.1
  apply finsum_eq_of_bijective e.symm e.symm.bijective
  intro η
  dsimp only
  have hlabel : correspondenceRemainingFiniteGenericLabel
      f g h i z w v x.1 (e.symm η) = η.1 :=
    congrArg Subtype.val (e.apply_symm_apply η)
  have hpoint : correspondenceRemainingFiniteModelProjection
      f g h i z w v x.1 (e.symm η).1 = η.1.1 :=
    congrArg Subtype.val hlabel
  rw [hlabel, hpoint]

end Stacks.Chow
