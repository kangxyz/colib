/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteTorEuler

/-! Literal endpoint consumers.  -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

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
    (hsr : RingTheory.Sequence.IsRegular ((pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1))) (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) (b n : ℕ) :
    let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
    Module.length B
      ((Koszul.seqComplexTensor (fun j => algebraMap R B (α (s j))) (M b)).homology n) ≠ ⊤ := by
  exact length_correspondenceRightRemainingFiniteTorKoszul_ne_top
    K f g h i z w v hz hw hv x s hsr hs b n

example
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v))
    {r : ℕ} (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s)) (J : Finset ℕ) :
    let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
    ∑ b ∈ J, (-1 : ℤ) ^ b * Koszul.seqEuler (fun j => α (s j))
      ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      ∑ᶠ q : {q : PrimeSpectrum B // IsMin q},
        (∑ b ∈ J, (-1 : ℤ) ^ b *
          ((Module.length (Localization.AtPrime q.1.asIdeal)
            (LocalizedModule q.1.asIdeal.primeCompl (M b))).toNat : ℤ)) *
              (Stacks.Length.primeResidueDegree (algebraMap R B)
                (q.1.asIdeal.comap (algebraMap R B)) q.1.asIdeal : ℤ) *
                  Koszul.seqEuler (fun j => α (s j))
                    (R ⧸ q.1.asIdeal.comap (algebraMap R B)) := by
  exact sum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_minimal
    K f g h i z w v hz hw hv x s hs J

example
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v))
    {r : ℕ} (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)))
    (hsr : RingTheory.Sequence.IsRegular ((pullback g g).presheaf.stalk
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
    letI := moduleFinite_correspondenceRightRemainingFiniteRing f g h i z w v hw hv x.1
    ∑ᶠ b : ℕ, (-1 : ℤ) ^ b * Koszul.seqEuler (fun j => α (s j))
      ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      ∑ᶠ q : MaximalSpectrum B,
        (∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
          Koszul.seqEuler
            (fun j => algebraMap B (Localization.AtPrime q.asIdeal)
              (algebraMap R B (α (s j))))
            (Localization.AtPrime q.asIdeal ⊗[B] M b)) *
              (Module.finiteAlgebraResidueDegree R B q : ℤ) := by
  exact finsum_signed_seqEuler_correspondenceRightRemainingFiniteTorModule_maximal
    K f g h i z w v hz hw hv x s hsr hs

end Stacks.Chow
