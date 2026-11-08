/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingPrimeTorComparison

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : correspondenceLeftImageIncidence f g h i z w v)

local notation3 (prettyPrint := false) "e" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v x
local notation3 (prettyPrint := false) "m" =>
  correspondenceLeftImageMiddlePair f g h i z w v e
local notation3 (prettyPrint := false) "R" => correspondenceRemainingImageStalk f g h i z w v x
local notation3 (prettyPrint := false) "B" => correspondenceRemainingFiniteRing f g h i z w v x
local notation3 (prettyPrint := false) "A" => (pullback h h).presheaf.stalk m
local notation3 (prettyPrint := false) "C" =>
  correspondenceRemainingAmbientStalk f g h i z w v x
local notation3 (prettyPrint := false) "α" =>
  correspondenceRemainingImageMiddleStalkMap f g h i z w v x

example [Smooth h] [IsSeparated h] :
    ∃ (r : ℕ) (s : Fin r → A), IsRegular A (List.ofFn s) ∧
      IdealSheafData.stalk (pullback.diagonal h).ker m = Ideal.span (Set.range s) :=
  exists_correspondenceRemainingOriginalMiddleList f g h i z w v x

example (q : PrimeSpectrum B) :
    IdealSheafData.stalk (correspondenceRemainingImagePrimeClosure f g h i z w v x q) e =
      (correspondenceRemainingImagePrime f g h i z w v x q).asIdeal :=
  correspondenceRemainingImagePrimeClosure_stalk f g h i z w v x q

example [Flat f] [Flat i] [IsSeparated h]
    (q : PrimeSpectrum B) {r : ℕ} (s : Fin r → A) (hr : IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker m = Ideal.span (Set.range s)) (n : ℕ) :
    Module.length C (correspondenceRemainingImagePrimeTor f g h i z w v x q n) =
      Module.length R ((Koszul.seqComplexTensor (fun j => α (s j))
        (R ⧸ (correspondenceRemainingImagePrime f g h i z w v x q).asIdeal)).homology n) :=
  length_correspondenceRemainingImagePrimeTor f g h i z w v x q s hr hs n

example [Flat f] [Flat i] [IsSeparated h] (q : PrimeSpectrum B) {r : ℕ}
    (s : Fin r → A) (hr : IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker m = Ideal.span (Set.range s)) :
    Koszul.seqEuler (fun j => α (s j))
        (R ⧸ (correspondenceRemainingImagePrime f g h i z w v x q).asIdeal) =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        ((Module.length C
          (correspondenceRemainingImagePrimeTor f g h i z w v x q n)).toNat : ℤ) :=
  seqEuler_correspondenceRemainingImagePrime_eq_finsum_tor f g h i z w v x q s hr hs
