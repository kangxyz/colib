/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTorLabels
public import
  Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteResidueTransport

/-!
# Actual weighted Euler formula over the original exterior labels

Combine the canonical full finite Tor family with the actual generic-label
bijection, the degreewise flat-local multiplicity comparison, and the residue
transport for the canonical affine algebra action. The resulting summand uses
the original pair's signed Tor coefficient, the full exterior fibre length,
and the actual original exterior finite morphism's residue degree. Its quotient
is at the literal image point in the actual image-stalk spectrum.

All original Tor degrees and retained exterior generic labels occur. Labels
with the same image are not identified. The finite map is not assumed flat,
and neither source nor exterior product is reduced. The identity is an integer
Euler formula, not yet a global cycle comparison. Regrouping exterior labels
by original pair-image components and identifying the remaining quotient Euler
with the corresponding image-component Tor cycle are separate comparisons.
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
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) (hv :
    IsFiniteCorrespondencePoint h i v)

include hz hw hv

/-- The actual whole-family integer Euler formula with original scheme residue weights.
Every original exterior label is retained, with its full nonreduced fibre multiplicity. -/
theorem finsum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_weightedLabels
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
        (correspondenceIncidenceTorCoefficient k g h i w v
          (correspondenceRightExteriorGenericLabel f g h i z w v η.1) *
          (correspondenceRightExteriorFiberLength f g h i z w v η.1.1 : ℤ)) *
          ((correspondenceRightIntermediateImageMap f g h i z w v).residueDegree η.1.1 : ℤ) *
          Koszul.seqEuler (fun j => α (s j))
            (R ⧸ (correspondenceRightRemainingFiniteModelStructure f g h i z w v x.1 q.1).asIdeal)
              := by
  dsimp only
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
  refine (finsum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_originalLabels
    k f g h i z w v hz hw hv x s hs).trans ?_
  apply finsum_congr
  intro η
  let e := correspondenceRightRemainingFiniteGenericEquivOriginal f g h i z w v x.1
  let q := e.symm η
  have hlabel : correspondenceRightRemainingFiniteGenericLabel
      f g h i z w v x.1 q = η.1 :=
    congrArg Subtype.val (e.apply_symm_apply η)
  have hpoint : correspondenceRightRemainingFiniteModelProjection
      f g h i z w v x.1 q.1 = η.1.1 :=
    congrArg Subtype.val hlabel
  let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
  let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
  let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
  let p := (correspondenceRightRemainingFiniteGenericEquivMinPrime
    f g h i z w v hw hv x.1 q).1
  let p' : PrimeSpectrum B := PrimeSpectrum.comap
    ((correspondenceRightRemainingFiniteModel f g h i z w v x.1).presheaf.germ
      ⊤ q.1 trivial).hom
    (IsLocalRing.closedPoint
      ((correspondenceRightRemainingFiniteModel f g h i z w v x.1).presheaf.stalk q.1))
  have hp : p = p' := PrimeSpectrum.ext
    (correspondenceRightRemainingFiniteGenericEquivMinPrime_asIdeal
      f g h i z w v hw hv x.1 q)
  have hdegree : Stacks.Length.primeResidueDegree (algebraMap R B)
      (p.asIdeal.comap (algebraMap R B)) p.asIdeal =
        (correspondenceRightIntermediateImageMap f g h i z w v).residueDegree η.1.1 := by
    exact (congrArg (fun t : PrimeSpectrum B =>
      Stacks.Length.primeResidueDegree (algebraMap R B)
        (t.asIdeal.comap (algebraMap R B)) t.asIdeal) hp).trans
      ((primeResidueDegree_correspondenceRightRemainingFiniteAlgebra
        f g h i z w v hw hv x.1 q.1).trans
          (congrArg (fun t =>
            (correspondenceRightIntermediateImageMap f g h i z w v).residueDegree t) hpoint))
  have hprime : p.asIdeal.comap (algebraMap R B) =
      (correspondenceRightRemainingFiniteModelStructure f g h i z w v x.1 q.1).asIdeal :=
    (congrArg (fun t : PrimeSpectrum B => t.asIdeal.comap (algebraMap R B)) hp).trans
      (correspondenceRightRemainingFiniteGermPrime_comap_algebraMap f g h i z w v x.1 q.1)
  exact congrArg₂ (fun (d : ℕ) (a : ℤ) =>
    (correspondenceIncidenceTorCoefficient k g h i w v
      (correspondenceRightExteriorGenericLabel f g h i z w v η.1) *
        (correspondenceRightExteriorFiberLength f g h i z w v η.1.1 : ℤ)) * (d : ℤ) * a)
    hdegree (congrArg (fun J : Ideal R =>
      Koszul.seqEuler (fun j => α (s j)) (R ⧸ J)) hprime)

end Stacks.Chow
