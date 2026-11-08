/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageComponentTor

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i) (t : correspondenceIncidence f g h z w)

local notation3 (prettyPrint := false) "q" => correspondenceIncidenceMap f g h z w t
local notation3 (prettyPrint := false) "P" => correspondenceSupportProduct f h i q v
local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "D" => correspondenceRemainingImageComponent f g h i z w v t
local notation3 (prettyPrint := false) "u" =>
  correspondenceRemainingSupportToImageExterior f g h i z w v t
local notation3 (prettyPrint := false) "mT" => correspondenceLeftImageMiddlePair f g h i z w v
local notation3 (prettyPrint := false) "mP" => correspondenceMiddlePair f h i
local notation3 (prettyPrint := false) "ι" => correspondenceSupportProductInclusion f h i q v

variable (y : correspondenceIncidence f h i q v)

local notation3 (prettyPrint := false) "x" =>
  correspondenceRemainingPairToImageIncidence f g h i z w v t y
local notation3 (prettyPrint := false) "e" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v x
local notation3 (prettyPrint := false) "p" => correspondenceIncidenceToSupportProduct f h i q v y
local notation3 (prettyPrint := false) "c" => correspondenceIncidenceAmbientInclusion f h i q v y
local notation3 (prettyPrint := false) "R" => correspondenceRemainingImageStalk f g h i z w v x
local notation3 (prettyPrint := false) "B" => (P).presheaf.stalk p
local notation3 (prettyPrint := false) "A" => (pullback h h).presheaf.stalk (mT e)
local notation3 (prettyPrint := false) "A₀" => (pullback h h).presheaf.stalk (mP c)
local notation3 (prettyPrint := false) "C" => correspondenceIncidenceAmbientStalk f h i q v y
local notation3 (prettyPrint := false) "I" => IdealSheafData.stalk D e
local notation3 (prettyPrint := false) "M" =>
  correspondenceRemainingImageComponentStalk f g h i z w v x t
local notation3 (prettyPrint := false) "α" =>
  correspondenceRemainingImageMiddleStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "φ" => correspondenceIncidenceSupportStalkMap f h i q v y
local notation3 (prettyPrint := false) "β" => ((mP).stalkMap c).hom

local notation3 (prettyPrint := false) "σ" =>
  correspondenceRemainingPairImageSupportStalkMap f g h i z w v t y
local notation3 (prettyPrint := false) "ε" =>
  correspondenceRemainingPairMiddleStalkIso f g h i z w v t y

example : (σ).comp α = (φ).comp ((β).comp (ε).hom.hom) :=
  correspondenceRemainingPairImageSupportStalkMap_middle f g h i z w v t y

example : letI : Algebra R B := (σ).toAlgebra; M ≃ₐ[R] B :=
  correspondenceRemainingPairImageQuotientAlgEquiv f g h i z w v t y

example
    [Flat f] [Flat i] [IsSeparated h] {r : ℕ} (s : Fin r → A)
    (hsr : IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker (mT e) = Ideal.span (Set.range s))
    (n : ℕ) :
    Module.length R ((Koszul.seqComplexTensor (fun j => α (s j)) M).homology n) =
      Module.length C (correspondenceIncidenceAmbientTor f h i q v y n) :=
  length_correspondenceRemainingPairImageKoszul_eq_Tor f g h i z w v t y s hsr hs n

example
    [Flat f] [Flat i] [IsSeparated h] {r : ℕ} (s : Fin r → A)
    (hsr : IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker (mT e) = Ideal.span (Set.range s)) :
    Koszul.seqEuler (fun j => α (s j)) M =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        ((Module.length C (correspondenceIncidenceAmbientTor f h i q v y n)).toNat : ℤ) :=
  seqEuler_correspondenceRemainingPairImage_eq_finsum_Tor f g h i z w v t y s hsr hs

example
    [Flat f] [Flat i] [Smooth h] [IsSeparated h] :
    ∃ (r : ℕ) (s : Fin r → A),
      IsRegular A (List.ofFn s) ∧
      IdealSheafData.stalk (pullback.diagonal h).ker (mT e) = Ideal.span (Set.range s) ∧
      Koszul.seqEuler (fun j => α (s j)) M =
        ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
          ((Module.length C (correspondenceIncidenceAmbientTor f h i q v y n)).toNat : ℤ) :=
  exists_correspondenceRemainingPairImage_originalList_Tor f g h i z w v t y

end Stacks.Chow
