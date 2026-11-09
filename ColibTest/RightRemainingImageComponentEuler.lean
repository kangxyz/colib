/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImageComponentEuler

/-! Literal endpoint consumers.  -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example
    (x : correspondenceRightImageIncidence f g h i z w v)
    (t : correspondenceIncidence g h i w v)
    [IsLocallyNoetherian (correspondenceRightIntermediateImageProduct f g h i z w v)]
    (p : {p : PrimeSpectrum (correspondenceRightRemainingImageStalk f g h i z w v x) // IsMin p})
      (hp : (IdealSheafData.stalk (correspondenceRightRemainingImageComponent f g h i z w v t)
      (correspondenceRightImageIncidenceInclusion f g h i z w v x)) ≤ p.1.asIdeal) :
    Module.length (Localization.AtPrime p.1.asIdeal)
      (LocalizedModule p.1.asIdeal.primeCompl
        (correspondenceRightRemainingImageComponentStalk f g h i z w v x t)) ≠ ⊤  := by
  exact length_correspondenceRightRemainingImageComponentStalk_ne_top
    f g h i z w v x t p hp

open Classical in
example
    (x : correspondenceRightImageIncidence f g h i z w v)
    (t : correspondenceIncidence g h i w v)
    [IsSeparated g] [IsLocallyNoetherian (correspondenceRightIntermediateImageProduct f g h i z w
      v)]
    (hx : x ∈ genericPoints (correspondenceRightImageIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x)))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x)) = Ideal.span (Set.range s)) :
    let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let R := correspondenceRightRemainingImageStalk f g h i z w v x
    let D := correspondenceRightRemainingImageComponent f g h i z w v t
    let I := IdealSheafData.stalk D x₀
    Koszul.seqEuler
      (fun j => correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x (s j))
      (correspondenceRightRemainingImageComponentStalk f g h i z w v x t) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        if hp : I ≤ p.1.asIdeal then
          componentMultiplicity (D).subschemeι
            (correspondenceRightRemainingImageComponentGenericLabel f g h i z w v x t p hp) *
              Koszul.seqEuler
                (fun j => correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x (s j))
                (R ⧸ p.1.asIdeal)
        else 0  := by
  exact seqEuler_correspondenceRightRemainingImageComponentStalk
    f g h i z w v x t hx s hs

end Stacks.Chow
