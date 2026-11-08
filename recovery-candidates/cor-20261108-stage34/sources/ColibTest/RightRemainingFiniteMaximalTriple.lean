/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteMaximalTriple

/-! Literal endpoint consumers. Source-only; no compilation or kernel check performed. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence
open Stacks.ModuleStalkSpecialization
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
  (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)

include hw hv

example
    (x : genericPoints (correspondenceRightImageIncidence f g h i z w v))
    (p : MaximalSpectrum (correspondenceRightRemainingFiniteRing f g h i z w v x.1)) :
    let R := correspondenceRightRemainingImageStalk f g h i z w v x.1
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x.1
    let A := (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x.1))
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x.1
    let M := correspondenceRightRemainingFiniteTorModule f g h i z w v x.1
    let y := (correspondenceRightRemainingFiniteMaximalEquivGenericTriple
      f g h i z w v hw hv x.1 x.2 p).1
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x.1
    ∀ {r : ℕ} (s : Fin r → A) (hsr : IsRegular A (List.ofFn s))
      (hs : IdealSheafData.stalk (pullback.diagonal g).ker
        (correspondenceRightImageMiddlePair f g h i z w v
          (correspondenceRightImageIncidenceInclusion f g h i z w v x.1)) =
            Ideal.span (Set.range s)),
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * Koszul.seqEuler
        (fun j => algebraMap B (Localization.AtPrime p.asIdeal)
          (algebraMap R B (α (s j))))
        (Localization.AtPrime p.asIdeal ⊗[B] M n)) =
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v y.1)
            (correspondenceTripleIncidenceTor f g h i z w v y.1 n)).toNat : ℤ) := by
  exact finsum_signed_correspondenceRightRemainingFiniteMaximalEuler_eq_tripleTor
    K f g h i z w v hw hv x p

end Stacks.Chow
