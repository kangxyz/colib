/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteWeightedComparison
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteGenericFibre

/-!
# Weighted remaining coefficients indexed by the actual generic triple fibre

The maximal-localization formula is reindexed by the proved bijection with the actual
original generic triple-incidence fibre. Its quotient residue degree is identified with
the prime residue degree, then with the actual triple-to-image morphism's residue degree.
The coefficient is still the genuine localized remaining Koszul Euler of the canonical
whole Tor family. In particular it is not named or assumed to be the triple Tor coefficient.

Every original fibre point is retained, including distinct labels with the same image.
There is no algebraic-closure, perfectness, reducedness, connectedness or finite-map
flatness hypothesis. The residue comparison uses native quotient-to-residue equivalences
and `Algebra.finrank_eq_of_equiv_equiv`; its square is checked on original base scalars.
The geometric label and degree identifications are the existing actual finite-model ones.

References: Stacks 02M0 for finite-algebra lengths and 02R4 for finite-cycle residue
weights. The original coefficient passage is in motivic revision
`a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Correspondences/Composition/Cycles/FirstStageWeightedRemainingCoefficient.lean`,
blob `3ae09238bac659f48c9e4beb21004af8f02ffd84`.
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
  (v : pullback (C := Scheme) h i) [IsSeparated h]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)

/-- The quotient degree in native finite pushforward is the prime degree for the actual
finite algebra action. This checks the residue-field scalar square, not only field carriers. -/
theorem finiteAlgebraResidueDegree_correspondenceRemainingFiniteRing_eq_prime
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : MaximalSpectrum (correspondenceRemainingFiniteRing f g h i z w v x)) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
    letI := moduleFinite_correspondenceRemainingFiniteRing f g h i z w v hz hw x
    Module.finiteAlgebraResidueDegree (correspondenceRemainingImageStalk f g h i z w v x)
      (correspondenceRemainingFiniteRing f g h i z w v x) q =
      Stacks.Length.primeResidueDegree
        (algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
          (correspondenceRemainingFiniteRing f g h i z w v x))
        (q.asIdeal.comap (algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
          (correspondenceRemainingFiniteRing f g h i z w v x))) q.asIdeal := by
  let R := correspondenceRemainingImageStalk f g h i z w v x
  let B := correspondenceRemainingFiniteRing f g h i z w v x
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x
  let := moduleFinite_correspondenceRemainingFiniteRing f g h i z w v hz hw x
  have hc : q.asIdeal.comap (algebraMap R B) = IsLocalRing.maximalIdeal R :=
    Module.finiteAlgebra_maximal_under R B q
  change Module.finiteAlgebraResidueDegree R B q = _
  rw [hc, Stacks.Length.primeResidueDegree_of_eq _ _ _ hc.symm]
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
theorem finiteAlgebraResidueDegree_correspondenceRemainingFiniteMaximalEquivGenericTriple
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (hx : x ∈ genericPoints (correspondenceLeftImageIncidence f g h i z w v))
    (q : MaximalSpectrum (correspondenceRemainingFiniteRing f g h i z w v x)) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
    letI := moduleFinite_correspondenceRemainingFiniteRing f g h i z w v hz hw x
    Module.finiteAlgebraResidueDegree (correspondenceRemainingImageStalk f g h i z w v x)
      (correspondenceRemainingFiniteRing f g h i z w v x) q =
      (correspondenceTripleToLeftImageIncidence f g h i z w v).residueDegree
        (correspondenceRemainingFiniteMaximalEquivGenericTriple f g h i z w v hz hw x hx q).1.1
    := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x
  let := moduleFinite_correspondenceRemainingFiniteRing f g h i z w v hz hw x
  exact (finiteAlgebraResidueDegree_correspondenceRemainingFiniteRing_eq_prime
    f g h i z w v hz hw x q).trans
      (primeResidueDegree_correspondenceRemainingFiniteMaximalEquivGenericTriple
        f g h i z w v hz hw x hx q)

end ResidueDegree

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (hv : IsFiniteCorrespondencePoint h i v)

include hz hw hv

/-- Every original generic triple-fibre label contributes its actual localized first-family
Euler and its original triple-to-image degree. No label or nilpotent structure is discarded. -/
theorem correspondenceLeftWeightedRemainingCycle_eq_finsum_genericTripleEuler
    (x : genericPoints (correspondenceLeftImageIncidence f g h i z w v))
    [LocallyOfFiniteType (correspondenceIntermediateImageTarget f g h z w ≫ h)] [LocallyOfFiniteType
        (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    {r : ℕ} (s : Fin r → ((pullback h h).presheaf.stalk (correspondenceLeftImageMiddlePair f g h i z
        w v (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1)))) (hsr : IsRegular
        ((pullback h h).presheaf.stalk (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1))) (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v (correspondenceLeftImageIncidenceInclusion f
          g h i z w v x.1)) = Ideal.span (Set.range s)) :
    let R := correspondenceRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRemainingFiniteRing f g h i z w v x.1
    let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRemainingFiniteTorModule f g h i z w v x.1
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
    letI := moduleFinite_correspondenceRemainingFiniteRing f g h i z w v hz hw x.1
    correspondenceLeftWeightedRemainingCycle f g h i z w v hw hv x.1 =
      ∑ᶠ y : {y : genericPoints (correspondenceTripleIncidence f g h i z w v) //
        correspondenceTripleToLeftImageIncidence f g h i z w v y.1 = x.1},
        let q := (correspondenceRemainingFiniteMaximalEquivGenericTriple
          f g h i z w v hz hw x.1 x.2).symm y
        (∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
          Koszul.seqEuler
            (fun j => algebraMap B (Localization.AtPrime q.asIdeal)
              (algebraMap R B (α (s j))))
            (Localization.AtPrime q.asIdeal ⊗[B] M b)) *
              ((correspondenceTripleToLeftImageIncidence f g h i z w v).residueDegree y.1.1 : ℤ)
    := by
  dsimp only
  let R := correspondenceRemainingImageStalk f g h i z w v x.1
  let B := correspondenceRemainingFiniteRing f g h i z w v x.1
  let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1
  let M := correspondenceRemainingFiniteTorModule f g h i z w v x.1
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
  let := moduleFinite_correspondenceRemainingFiniteRing f g h i z w v hz hw x.1
  let e := correspondenceRemainingFiniteMaximalEquivGenericTriple
    f g h i z w v hz hw x.1 x.2
  rw [correspondenceLeftWeightedRemainingCycle_eq_finsum_maximalEuler
    K f g h i z w v hz hw x hv s hsr hs]
  rw [← finsum_comp_equiv e]
  apply finsum_congr
  intro q
  dsimp only
  rw [e.symm_apply_apply,
    finiteAlgebraResidueDegree_correspondenceRemainingFiniteMaximalEquivGenericTriple
      f g h i z w v hz hw x.1 x.2 q]

end Stacks.Chow
