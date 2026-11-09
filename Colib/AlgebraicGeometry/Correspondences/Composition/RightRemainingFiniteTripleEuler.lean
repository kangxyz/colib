/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteMaximalTriple
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTorEuler
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightTripleTorPushforward

/-!
# The whole actual right Tor-family Euler is the pushed original triple-Tor coefficient

The genuine all-degree maximal-localization formula is identified term by term with
actual original triple Tor. Native quotient/residue field comparison preserves each
finite-algebra residue degree, and the full maximal-to-generic-triple-fibre equivalence
reindexes without discarding labels. The remaining Y list is the same original regular
list on both sides. The coefficient family and all degree bounds are actual constructions.

This closes the local-family-to-triple side. Identifying that actual whole-family Euler
with the labelled weighted remaining cycle still requires image-component replacement;
no such equality is assumed or asserted here. Fields remain arbitrary and smooth factors
may be disconnected. References: Stacks 02M0, 02R4, 0098, 0AZT, and local 0B1L.
-/

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

/-- The quotient degree in native finite pushforward is the prime degree for the actual
finite algebra action. This checks the residue-field scalar square, not only field carriers. -/
theorem finiteAlgebraResidueDegree_correspondenceRightRemainingFiniteRing_eq_prime
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
  let R := correspondenceRightRemainingImageStalk f g h i z w v x
  let B := correspondenceRightRemainingFiniteRing f g h i z w v x
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
  let := moduleFinite_correspondenceRightRemainingFiniteRing f g h i z w v hw hv x
  have hc : q.asIdeal.comap (algebraMap R B) = IsLocalRing.maximalIdeal R :=
    Module.finiteAlgebra_maximal_under R B q
  have hc' : PrimeSpectrum.comap (algebraMap R B) q.toPrimeSpectrum =
      IsLocalRing.closedPoint R := PrimeSpectrum.ext hc
  refine Eq.trans ?_ (congrArg (fun p : PrimeSpectrum R =>
    Stacks.Length.primeResidueDegree (algebraMap R B) p.asIdeal q.asIdeal) hc').symm
  refine Eq.trans ?_ (Stacks.Length.primeResidueDegree_of_eq
    (algebraMap R B) (IsLocalRing.maximalIdeal R) q.asIdeal hc.symm).symm
  let m := IsLocalRing.maximalIdeal R
  let φ := Ideal.ResidueField.map m q.asIdeal (algebraMap R B) hc.symm
  let := φ.toAlgebra
  let eR : IsLocalRing.ResidueField R ≃+* m.ResidueField :=
    RingEquiv.ofBijective (algebraMap (R ⧸ m) m.ResidueField)
      m.bijective_algebraMap_quotient_residueField
  let eB := Module.finiteAlgebraResidueQuotientEquiv (S := B) q
  refine Algebra.finrank_eq_of_equiv_equiv eR eB.toRingEquiv (RingHom.ext fun a => ?_)
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := R) a
  have heR : eR (IsLocalRing.residue R a) = algebraMap R m.ResidueField a := by
    change algebraMap (R ⧸ m) m.ResidueField (algebraMap R (R ⧸ m) a) = _
    exact (IsScalarTower.algebraMap_apply R (R ⧸ m) m.ResidueField a).symm
  change φ (eR (IsLocalRing.residue R a)) =
    eB (algebraMap (IsLocalRing.ResidueField R) (B ⧸ q.asIdeal) (IsLocalRing.residue R a))
  rw [heR, Ideal.ResidueField.map_algebraMap]
  change algebraMap B q.asIdeal.ResidueField (algebraMap R B a) =
    eB (algebraMap (IsLocalRing.ResidueField R) (B ⧸ q.asIdeal)
      (algebraMap R (IsLocalRing.ResidueField R) a))
  rw [← IsScalarTower.algebraMap_apply R (IsLocalRing.ResidueField R) (B ⧸ q.asIdeal),
    IsScalarTower.algebraMap_apply R B (B ⧸ q.asIdeal)]
  exact (eB.commutes (algebraMap R B a)).symm

/-- The finite-pushforward degree is exactly the degree of the original triple-to-image map. -/
theorem finiteAlgebraResidueDegree_correspondenceRightRemainingFiniteMaximalEquivGenericTriple
    [IsSeparated g]
    (x : correspondenceRightImageIncidence f g h i z w v)
    (hx : x ∈ genericPoints (correspondenceRightImageIncidence f g h i z w v))
    (q : MaximalSpectrum (correspondenceRightRemainingFiniteRing f g h i z w v x)) :
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
    letI := moduleFinite_correspondenceRightRemainingFiniteRing f g h i z w v hw hv x
    Module.finiteAlgebraResidueDegree (correspondenceRightRemainingImageStalk f g h i z w v x)
      (correspondenceRightRemainingFiniteRing f g h i z w v x) q =
      (correspondenceTripleToRightImageIncidence f g h i z w v).residueDegree
        (correspondenceRightRemainingFiniteMaximalEquivGenericTriple f g h i z w v hw hv x hx q).1.1
    := by
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
  let := moduleFinite_correspondenceRightRemainingFiniteRing f g h i z w v hw hv x
  exact (finiteAlgebraResidueDegree_correspondenceRightRemainingFiniteRing_eq_prime
    f g h i z w v hw hv x q).trans
      (primeResidueDegree_correspondenceRightRemainingFiniteMaximalEquivGenericTriple
        f g h i z w v hw hv x hx q)

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

/-- Whole-family Euler for the original Y list is the actual pushed triple-Tor coefficient. -/
theorem finsum_signed_correspondenceRightRemainingFiniteTorEuler_eq_tripleTorPushforward
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
  dsimp only
  let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
  let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
  let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
  let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
  let := moduleFinite_correspondenceRightRemainingFiniteRing f g h i z w v hw hv x.1
  let := isFinite_correspondenceTripleToRightImageIncidence f g h i z w v hw hv
  let e := correspondenceRightRemainingFiniteMaximalEquivGenericTriple
    f g h i z w v hw hv x.1 x.2
  rw [finsum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_maximal
    K f g h i z w v hz hw hv x s hsr hs]
  rw [rightTripleTorPushforward_apply_generic K f g h i z w v hw hv x]
  rw [← finsum_comp_equiv e]
  apply finsum_congr
  intro p
  rw [finsum_signed_correspondenceRightRemainingFiniteMaximalEuler_eq_tripleTor
    (K := K) f g h i z w v hw hv x p s hsr hs,
    finiteAlgebraResidueDegree_correspondenceRightRemainingFiniteMaximalEquivGenericTriple
      f g h i z w v hw hv x.1 x.2 p]

end Stacks.Chow
