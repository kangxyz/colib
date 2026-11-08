/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingWeightedTripleLabels
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteTorStalkEuler
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteFirstKoszulEuler
public import Colib.AlgebraicGeometry.Correspondences.Composition.ActualPairColumnCombinedEuler
public import Colib.AlgebraicGeometry.Correspondences.Composition.PairOriginalMiddleList

/-!
# The genuine weighted remaining coefficient is the pushed triple-Tor coefficient

At each generic point of the whole remaining image incidence, the literal weighted
remaining native cycle has coefficient equal to the sum of actual combined-diagonal
triple Tor coefficients over its original generic triple fibre, weighted by the actual
triple-to-image residue degrees. Both Tor indices retain every signed contribution.

The construction uses the full finite coordinate algebra and its canonical Tor-sheaf
section family. All maximal labels are identified with original triple-fibre points.
Affine tensor localization, actual stalk-ring transport, and the exact original Y/Z-list
comparisons identify each remaining Euler with the original first-Koszul column Euler.
Public native regular-local Tor associativity, with the diagonal quotients ordered first,
then collapses the diagonal-quotient Tor to the actual combined diagonal. No module family,
scalar comparison, finite-length witness, cutoff, or coefficient equality is assumed.

The base field is arbitrary and smooth schemes may be disconnected. The finite model,
exterior support and first-stage stalks retain their nilpotents; finite maps are not
assumed flat. The regular remaining list is chosen in its original middle-pair stalk.

This is the generic whole-image coefficient theorem. Extending it to a global cycle
identity also requires the nongeneric support argument; constructing the Cor category
and its bilinear associativity is not asserted by this file.

References: Stacks 02M0 (finite-algebra length), 02R4 (finite pushforward), 0AZT (Tor stalks),
and the arbitrary-ring local statement of 0B1L implemented by
`Stacks.Intersection.finsum_alternating_length_tor_assoc_of_isRegularLocalRing`.
Implementation comparison: independent motivic `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Correspondences/Composition/Cycles/FirstStageWeightedRemainingCoefficient.lean`,
blob `3ae09238bac659f48c9e4beb21004af8f02ffd84`, lines 107-245. The current proof consumes
native exterior-power Koszul complexes and native Tor rather than the old recursive model.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingTheory.Sequence Stacks.ModuleStalkSpecialization
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

private theorem regular_remaining_stalkCongr {T : Scheme.{u}} {a b : T} (hab : a = b)
    {r : ℕ} (s : Fin r → T.presheaf.stalk a)
    (hs : IsRegular (T.presheaf.stalk a) (List.ofFn s)) :
    IsRegular (T.presheaf.stalk b)
      (List.ofFn (fun j => (T.presheaf.stalkCongr (Inseparable.of_eq hab)).hom (s j))) := by
  subst b
  simpa [TopCat.Presheaf.stalkCongr] using hs

private theorem ideal_remaining_stalkCongr {T : Scheme.{u}} (I : T.IdealSheafData)
    {a b : T} (hab : a = b) {r : ℕ} (s : Fin r → T.presheaf.stalk a)
    (hs : IdealSheafData.stalk I a = Ideal.span (Set.range s)) :
    IdealSheafData.stalk I b = Ideal.span
      (Set.range (fun j => (T.presheaf.stalkCongr (Inseparable.of_eq hab)).hom (s j))) := by
  subst b
  simpa [TopCat.Presheaf.stalkCongr] using hs

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)

include hz hw

/-- Every maximal localization of the actual finite family computes actual combined triple
Tor at its original generic triple label. All scalar and coefficient comparisons are constructed. -/
theorem finsum_signed_correspondenceRemainingFiniteMaximalEuler_eq_tripleTor
    (x : genericPoints (correspondenceLeftImageIncidence f g h i z w v))
    (p : MaximalSpectrum (correspondenceRemainingFiniteRing f g h i z w v x.1)) :
    let R := correspondenceRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRemainingFiniteRing f g h i z w v x.1
    let A := (pullback h h).presheaf.stalk
      (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1))
    let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRemainingFiniteTorModule f g h i z w v x.1
    let y := (correspondenceRemainingFiniteMaximalEquivGenericTriple
      f g h i z w v hz hw x.1 x.2 p).1
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
    ∀ {r : ℕ} (s : Fin r → A) (hsr : IsRegular A (List.ofFn s))
      (hs : IdealSheafData.stalk (pullback.diagonal h).ker
        (correspondenceLeftImageMiddlePair f g h i z w v
          (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1)) =
            Ideal.span (Set.range s)),
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * Koszul.seqEuler
        (fun j => algebraMap B (Localization.AtPrime p.asIdeal)
          (algebraMap R B (α (s j))))
        (Localization.AtPrime p.asIdeal ⊗[B] M n)) =
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v y.1)
            (correspondenceTripleIncidenceTor f g h i z w v y.1 n)).toNat : ℤ) := by
  dsimp only
  intro r s hsr hs
  let R := correspondenceRemainingImageStalk f g h i z w v x.1
  let B := correspondenceRemainingFiniteRing f g h i z w v x.1
  let E := correspondenceRemainingFiniteModel f g h i z w v x.1
  let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1
  let M := correspondenceRemainingFiniteTorModule f g h i z w v x.1
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
  let := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x.1
  let : IsLocallyNoetherian (correspondenceIntersectionAmbient f g h) :=
    LocallyOfFiniteType.isLocallyNoetherian (correspondenceIntersectionAmbientToField K f g h)
  let q := (correspondenceRemainingFiniteClosedEquivMaximal
    f g h i z w v x.1 hz hw).symm p
  let y := (correspondenceRemainingFiniteMaximalEquivGenericTriple
    f g h i z w v hz hw x.1 x.2 p).1
  have hy : correspondenceTripleToLeftImageIncidence f g h i z w v y.1 = x.1 :=
    (correspondenceRemainingFiniteMaximalEquivGenericTriple
      f g h i z w v hz hw x.1 x.2 p).2
  have hρ : correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y.1 =
      correspondenceRemainingFiniteModelProjection f g h i z w v x.1 q.1 := by
    exact correspondenceRemainingFiniteMaximalEquivTriple_projection
      f g h i z w v x.1 hz hw p
  have hprime : ((isAffineOpen_top E).primeIdealOf ⟨q.1, trivial⟩).asIdeal = p.asIdeal := by
    rw [(isAffineOpen_top E).primeIdealOf_eq_map_closedPoint]
    exact (correspondenceRemainingFiniteMaximalEquivTriple_germPrime
      f g h i z w v x.1 hz hw p).symm
  let eZ := (pullback h h).presheaf.stalkCongr (Inseparable.of_eq
    (correspondenceRemainingTriple_middle_point_eq f g h i z w v x.1 y.1 hy))
  let sZ := fun j => eZ.hom (s j)
  have hsZ := regular_remaining_stalkCongr
    (correspondenceRemainingTriple_middle_point_eq f g h i z w v x.1 y.1 hy) s hsr
  have hksZ := ideal_remaining_stalkCongr (pullback.diagonal h).ker
    (correspondenceRemainingTriple_middle_point_eq f g h i z w v x.1 y.1 hy) s hs
  obtain ⟨tLen, t, ht, hkt⟩ := exists_correspondenceIncidenceOriginalMiddleList f g h z w
    (correspondenceLeftExteriorProjection f g h i z w v
      (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y.1))
  let a₀ := correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y.1
  let p₀ := correspondenceIncidenceAmbientInclusion f g h z w
    (correspondenceLeftExteriorProjection f g h i z w v a₀)
  let l := List.ofFn (fun j => correspondenceTripleIncidencePairAmbientStalkMap f g h i z w v y.1
    ((correspondenceMiddlePair f g h).stalkMap p₀ (t j)))
  let hreg := correspondenceOriginalPairList_first_regular f g h i z w v y.1 t ht hkt
  let H := fun n => correspondenceRemainingFirstKoszulModule
    f g h i z w v y.1 l hreg.1 hreg.2 n
  let sP := fun j => correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v y.1
    ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y.1) (sZ j))
  have hlocal (n : ℕ) :
      Koszul.seqEuler
        (fun j => algebraMap B (Localization.AtPrime p.asIdeal) (algebraMap R B (α (s j))))
        (Localization.AtPrime p.asIdeal ⊗[B] M n) = Koszul.seqEuler sP (H n) := by
    let := stalkModule (correspondenceRemainingFiniteTorSheaf f g h i z w v x.1 n) q.1
    have h₁ := seqEuler_correspondenceRemainingFiniteTorTensor_eq_stalk
      f g h i z w v hz hw x.1 q.1 n (fun j => algebraMap R B (α (s j)))
    dsimp only at h₁
    rw [hprime] at h₁
    have h₂ := seqEuler_correspondenceRemainingFiniteTorStalk_eq_firstKoszul
      f g h i z w v x.1 q.1 q.2 y.1 hy hρ t ht hkt n sZ
    dsimp only at h₂
    have h₂' :
        Koszul.seqEuler (fun j => E.presheaf.germ ⊤ q.1 trivial
          (algebraMap R B (α (s j))))
          ((correspondenceRemainingFiniteTorSheaf f g h i z w v x.1 n).presheaf.stalk q.1) =
            Koszul.seqEuler sP (H n) := by
      simpa only [sZ, Iso.hom_inv_id_apply] using h₂
    exact h₁.trans h₂'

  calc
    _ = ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * Koszul.seqEuler sP (H n) := by
      apply finsum_congr
      intro n
      rw [hlocal]
    _ = _ := finsum_actualPair_remainingFirstEuler_eq_combinedTor
      K f g h i z w v y t ht hkt sZ hsZ hksZ

/-- The full weighted remaining coefficient is the actual residue-degree-weighted sum of
combined-diagonal triple Tor over its original generic fibre, with no chosen lists as inputs. -/
theorem correspondenceLeftWeightedRemainingCycle_eq_finsum_tripleTor
    (hv : IsFiniteCorrespondencePoint h i v)
    [LocallyOfFiniteType (correspondenceIntermediateImageTarget f g h z w ≫ h)]
    [LocallyOfFiniteType (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    (x : genericPoints (correspondenceLeftImageIncidence f g h i z w v)) :
    correspondenceLeftWeightedRemainingCycle f g h i z w v hw hv x.1 =
      ∑ᶠ y : {y : genericPoints (correspondenceTripleIncidence f g h i z w v) //
        correspondenceTripleToLeftImageIncidence f g h i z w v y.1 = x.1},
        (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v y.1.1)
            (correspondenceTripleIncidenceTor f g h i z w v y.1.1 n)).toNat : ℤ)) *
          ((correspondenceTripleToLeftImageIncidence f g h i z w v).residueDegree y.1.1 : ℤ) := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
  obtain ⟨r, s, hsr, hs⟩ := exists_correspondenceRemainingOriginalMiddleList f g h i z w v x.1
  rw [correspondenceLeftWeightedRemainingCycle_eq_finsum_genericTripleEuler
    K f g h i z w v hz hw hv x s hsr hs]
  apply finsum_congr
  intro y
  dsimp only
  rw [finsum_signed_correspondenceRemainingFiniteMaximalEuler_eq_tripleTor
    K f g h i z w v hz hw x _ s hsr hs]
  rw [Equiv.apply_symm_apply]

end Stacks.Chow
