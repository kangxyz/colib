/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageComponentTor

noncomputable section

set_option backward.isDefEq.respectTransparency true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i) (t : correspondenceIncidence f g h z w)

example
    (y : correspondenceIncidence f h i (correspondenceIncidenceMap f g h z w t) v) :
    let q := correspondenceIncidenceMap f g h z w t
    let mP := correspondenceMiddlePair f h i
    let x := correspondenceRemainingPairToImageIncidence f g h i z w v t y
    let c := correspondenceIncidenceAmbientInclusion f h i q v y
    let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x
    let φ := correspondenceIncidenceSupportStalkMap f h i q v y
    let β := (mP.stalkMap c).hom
    let σ := correspondenceRemainingPairImageSupportStalkMap f g h i z w v t y
    let ε := correspondenceRemainingPairMiddleStalkIso f g h i z w v t y
    (σ).comp α = (φ).comp ((β).comp (ε).hom.hom) := by
  let q := correspondenceIncidenceMap f g h z w t
  let mP := correspondenceMiddlePair f h i
  let x := correspondenceRemainingPairToImageIncidence f g h i z w v t y
  let c := correspondenceIncidenceAmbientInclusion f h i q v y
  let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x
  let φ := correspondenceIncidenceSupportStalkMap f h i q v y
  let β := (mP.stalkMap c).hom
  let σ := correspondenceRemainingPairImageSupportStalkMap f g h i z w v t y
  let ε := correspondenceRemainingPairMiddleStalkIso f g h i z w v t y
  exact correspondenceRemainingPairImageSupportStalkMap_middle f g h i z w v t y

example
    (y : correspondenceIncidence f h i (correspondenceIncidenceMap f g h z w t) v) :
    let q := correspondenceIncidenceMap f g h z w t
    let P := correspondenceSupportProduct f h i q v
    let x := correspondenceRemainingPairToImageIncidence f g h i z w v t y
    let p := correspondenceIncidenceToSupportProduct f h i q v y
    let R := correspondenceRemainingImageStalk f g h i z w v x
    let B := P.presheaf.stalk p
    let M := correspondenceRemainingImageComponentStalk f g h i z w v x t
    let σ := correspondenceRemainingPairImageSupportStalkMap f g h i z w v t y
    letI : Algebra R B := (σ).toAlgebra; M ≃ₐ[R] B := by
  let q := correspondenceIncidenceMap f g h z w t
  let P := correspondenceSupportProduct f h i q v
  let x := correspondenceRemainingPairToImageIncidence f g h i z w v t y
  let p := correspondenceIncidenceToSupportProduct f h i q v y
  let R := correspondenceRemainingImageStalk f g h i z w v x
  let B := P.presheaf.stalk p
  let M := correspondenceRemainingImageComponentStalk f g h i z w v x t
  let σ := correspondenceRemainingPairImageSupportStalkMap f g h i z w v t y
  exact correspondenceRemainingPairImageQuotientAlgEquiv f g h i z w v t y

example
    (y : correspondenceIncidence f h i (correspondenceIncidenceMap f g h z w t) v)
    [Flat f] [Flat i] [IsSeparated h] :
    let q := correspondenceIncidenceMap f g h z w t
    let mT := correspondenceLeftImageMiddlePair f g h i z w v
    let x := correspondenceRemainingPairToImageIncidence f g h i z w v t y
    let e := correspondenceLeftImageIncidenceInclusion f g h i z w v x
    let R := correspondenceRemainingImageStalk f g h i z w v x
    let A := (pullback h h).presheaf.stalk (mT e)
    let C := correspondenceIncidenceAmbientStalk f h i q v y
    let M := correspondenceRemainingImageComponentStalk f g h i z w v x t
    let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x
    ∀ {r : ℕ}
      (s : Fin r → A)
      (_hsr : IsRegular A (List.ofFn s))
      (_hs : IdealSheafData.stalk (pullback.diagonal h).ker (mT e) = Ideal.span (Set.range s))
      (n : ℕ),
      Module.length R ((Koszul.seqComplexTensor (fun j => α (s j)) M).homology n) =
        Module.length C (correspondenceIncidenceAmbientTor f h i q v y n) := by
  let q := correspondenceIncidenceMap f g h z w t
  let mT := correspondenceLeftImageMiddlePair f g h i z w v
  let x := correspondenceRemainingPairToImageIncidence f g h i z w v t y
  let e := correspondenceLeftImageIncidenceInclusion f g h i z w v x
  let R := correspondenceRemainingImageStalk f g h i z w v x
  let A := (pullback h h).presheaf.stalk (mT e)
  let C := correspondenceIncidenceAmbientStalk f h i q v y
  let M := correspondenceRemainingImageComponentStalk f g h i z w v x t
  let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x
  dsimp only
  intro r s hsr hs n
  exact length_correspondenceRemainingPairImageKoszul_eq_Tor f g h i z w v t y s hsr hs n

example
    (y : correspondenceIncidence f h i (correspondenceIncidenceMap f g h z w t) v)
    [Flat f] [Flat i] [IsSeparated h] :
    let q := correspondenceIncidenceMap f g h z w t
    let mT := correspondenceLeftImageMiddlePair f g h i z w v
    let x := correspondenceRemainingPairToImageIncidence f g h i z w v t y
    let e := correspondenceLeftImageIncidenceInclusion f g h i z w v x
    let A := (pullback h h).presheaf.stalk (mT e)
    let C := correspondenceIncidenceAmbientStalk f h i q v y
    let M := correspondenceRemainingImageComponentStalk f g h i z w v x t
    let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x
    ∀ {r : ℕ}
      (s : Fin r → A)
      (_hsr : IsRegular A (List.ofFn s))
      (_hs : IdealSheafData.stalk (pullback.diagonal h).ker (mT e) = Ideal.span (Set.range s)),
      Koszul.seqEuler (fun j => α (s j)) M =
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length C (correspondenceIncidenceAmbientTor f h i q v y n)).toNat : ℤ) := by
  let q := correspondenceIncidenceMap f g h z w t
  let mT := correspondenceLeftImageMiddlePair f g h i z w v
  let x := correspondenceRemainingPairToImageIncidence f g h i z w v t y
  let e := correspondenceLeftImageIncidenceInclusion f g h i z w v x
  let A := (pullback h h).presheaf.stalk (mT e)
  let C := correspondenceIncidenceAmbientStalk f h i q v y
  let M := correspondenceRemainingImageComponentStalk f g h i z w v x t
  let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x
  dsimp only
  intro r s hsr hs
  exact seqEuler_correspondenceRemainingPairImage_eq_finsum_Tor f g h i z w v t y s hsr hs

example
    (y : correspondenceIncidence f h i (correspondenceIncidenceMap f g h z w t) v)
    [Flat f] [Flat i] [Smooth h] [IsSeparated h] :
    let q := correspondenceIncidenceMap f g h z w t
    let mT := correspondenceLeftImageMiddlePair f g h i z w v
    let x := correspondenceRemainingPairToImageIncidence f g h i z w v t y
    let e := correspondenceLeftImageIncidenceInclusion f g h i z w v x
    let A := (pullback h h).presheaf.stalk (mT e)
    let C := correspondenceIncidenceAmbientStalk f h i q v y
    let M := correspondenceRemainingImageComponentStalk f g h i z w v x t
    let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x
    ∃ (r : ℕ) (s : Fin r → A),
      IsRegular A (List.ofFn s) ∧
      IdealSheafData.stalk (pullback.diagonal h).ker (mT e) = Ideal.span (Set.range s) ∧
      Koszul.seqEuler (fun j => α (s j)) M =
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length C (correspondenceIncidenceAmbientTor f h i q v y n)).toNat : ℤ) := by
  let q := correspondenceIncidenceMap f g h z w t
  let mT := correspondenceLeftImageMiddlePair f g h i z w v
  let x := correspondenceRemainingPairToImageIncidence f g h i z w v t y
  let e := correspondenceLeftImageIncidenceInclusion f g h i z w v x
  let A := (pullback h h).presheaf.stalk (mT e)
  let C := correspondenceIncidenceAmbientStalk f h i q v y
  let M := correspondenceRemainingImageComponentStalk f g h i z w v x t
  let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x
  exact exists_correspondenceRemainingPairImage_originalList_Tor f g h i z w v t y

end Stacks.Chow
