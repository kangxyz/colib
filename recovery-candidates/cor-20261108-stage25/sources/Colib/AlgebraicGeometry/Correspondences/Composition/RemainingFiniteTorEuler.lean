/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteTorBound
public import Colib.RingTheory.Koszul.EulerVanishing

/-!
# The unbounded signed Euler formula for the actual whole Tor family

The whole finite coefficient family has a genuine finite degree bound, proved
from its finitely many maximal localizations. Thus the integer alternating sums
in the first Tor degree can be written as finsums without an input cutoff.
Applying the proved finite-window generic devissage to this actual bound gives
an all-degree formula retaining every minimal source prime and original residue
degree. Neither the coefficient family nor its boundedness is a hypothesis.

The remaining ideal of definition still comes from the actual generic
remaining-image intersection. This is an actual local integer Euler formula;
it does not claim that the remaining quotient Euler factors are already the
global image-component intersection cycles.
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

/-- All original Tor degrees contribute through their actual modules, with no chosen finite
window. A genuine module bound, rather than cancellation, justifies both inner finsums. -/
theorem finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule {r : ℕ}
    (s : Fin r → A)
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
    ∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
      Koszul.seqEuler (fun j => α (s j))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      ∑ᶠ q : {q : PrimeSpectrum B // IsMin q},
        (∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
          ((Module.length (Localization.AtPrime q.1.asIdeal)
            (LocalizedModule q.1.asIdeal.primeCompl (M b))).toNat : ℤ)) *
              (Stacks.Length.primeResidueDegree (algebraMap R B)
                (q.1.asIdeal.comap (algebraMap R B)) q.1.asIdeal : ℤ) *
                  Koszul.seqEuler (fun j => α (s j))
                    (R ⧸ q.1.asIdeal.comap (algebraMap R B)) := by
  classical
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
  let : IsLocallyNoetherian (correspondenceIntersectionAmbient f g h) :=
    LocallyOfFiniteType.isLocallyNoetherian (correspondenceIntersectionAmbientToField k f g h)
  obtain ⟨d, hd⟩ := exists_correspondenceRemainingFiniteTorModule_degreeBound
    k f g h i z w v hz hw x.1
  have hleft : (∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
      Koszul.seqEuler (fun j => α (s j))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b))) =
      ∑ b ∈ Finset.range (d + 1), (-1 : ℤ) ^ b *
        Koszul.seqEuler (fun j => α (s j))
          ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) := by
    apply finsum_eq_sum_of_support_subset
    intro b hb
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    by_contra hbd
    let := ModuleCat.isZero_iff_subsingleton.mp (hd b (lt_of_not_ge hbd))
    apply hb
    rw [Koszul.seqEuler_eq_zero_of_subsingleton, mul_zero]
  have hright (q : {q : PrimeSpectrum B // IsMin q}) :
      (∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
        ((Module.length (Localization.AtPrime q.1.asIdeal)
          (LocalizedModule q.1.asIdeal.primeCompl (M b))).toNat : ℤ)) =
      ∑ b ∈ Finset.range (d + 1), (-1 : ℤ) ^ b *
        ((Module.length (Localization.AtPrime q.1.asIdeal)
          (LocalizedModule q.1.asIdeal.primeCompl (M b))).toNat : ℤ) := by
    apply finsum_eq_sum_of_support_subset
    intro b hb
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    by_contra hbd
    let := ModuleCat.isZero_iff_subsingleton.mp (hd b (lt_of_not_ge hbd))
    apply hb
    simp only [Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero, mul_zero]
  rw [hleft]
  simp_rw [hright]
  exact sum_signed_seqEuler_correspondenceRemainingFiniteTorModule
    f g h i z w v hz hw x s hs (Finset.range (d + 1))

end Stacks.Chow
