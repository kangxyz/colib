/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImageComponentTor

/-! Literal endpoint consumers.  -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

set_option backward.isDefEq.respectTransparency true

example
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t)) :
    let q := correspondenceIncidenceMap g h i w v t
    let P := correspondenceSupportProduct f g i z q
    let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
    let p := correspondenceIncidenceToSupportProduct f g i z q y
    let R := correspondenceRightRemainingImageStalk f g h i z w v x
    let B := P.presheaf.stalk p
    let M := correspondenceRightRemainingImageComponentStalk f g h i z w v x t
    let σ := correspondenceRightRemainingPairImageSupportStalkMap f g h i z w v t y
    letI : Algebra R B := (σ).toAlgebra
    M ≃ₐ[R] B  := by
  exact correspondenceRightRemainingPairImageQuotientAlgEquiv
    f g h i z w v t y

example
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t))
    [Flat f] [Flat i] [IsSeparated g] :
    let q := correspondenceIncidenceMap g h i w v t
    let mT := correspondenceRightImageMiddlePair f g h i z w v
    let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
    let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let R := correspondenceRightRemainingImageStalk f g h i z w v x
    let A := (pullback g g).presheaf.stalk (mT e)
    let C := correspondenceIncidenceAmbientStalk f g i z q y
    let M := correspondenceRightRemainingImageComponentStalk f g h i z w v x t
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
    ∀ {r : ℕ}
      (s : Fin r → A)
      (_hsr : IsRegular A (List.ofFn s))
      (_hs : IdealSheafData.stalk (pullback.diagonal g).ker (mT e) = Ideal.span (Set.range s))
      (n : ℕ),
      Module.length R ((Koszul.seqComplexTensor (fun j => α (s j)) M).homology n) =
        Module.length C (correspondenceIncidenceAmbientTor f g i z q y n)  := by
  exact length_correspondenceRightRemainingPairImageKoszul_eq_Tor
    f g h i z w v t y

example
    (t : correspondenceIncidence g h i w v)
    (y : correspondenceIncidence f g i z (correspondenceIncidenceMap g h i w v t))
    [Flat f] [Flat i] [IsSeparated g] :
    let q := correspondenceIncidenceMap g h i w v t
    let mT := correspondenceRightImageMiddlePair f g h i z w v
    let x := correspondenceRightRemainingPairToImageIncidence f g h i z w v t y
    let e := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let A := (pullback g g).presheaf.stalk (mT e)
    let C := correspondenceIncidenceAmbientStalk f g i z q y
    let M := correspondenceRightRemainingImageComponentStalk f g h i z w v x t
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
    ∀ {r : ℕ}
      (s : Fin r → A)
      (_hsr : IsRegular A (List.ofFn s))
      (_hs : IdealSheafData.stalk (pullback.diagonal g).ker (mT e) = Ideal.span (Set.range s)),
      Koszul.seqEuler (fun j => α (s j)) M =
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length C (correspondenceIncidenceAmbientTor f g i z q y n)).toNat : ℤ)  := by
  exact seqEuler_correspondenceRightRemainingPairImage_eq_finsum_Tor
    f g h i z w v t y

end Stacks.Chow
