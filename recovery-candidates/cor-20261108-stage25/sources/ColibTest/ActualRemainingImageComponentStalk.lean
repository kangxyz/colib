/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageComponentStalk

noncomputable section

set_option backward.isDefEq.respectTransparency true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i) (t : correspondenceIncidence f g h z w)

local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "D" => correspondenceRemainingImageComponent f g h i z w v t
local notation3 (prettyPrint := false) "P" =>
  correspondenceSupportProduct f h i (correspondenceIncidenceMap f g h z w t) v
local notation3 (prettyPrint := false) "j" => correspondenceLeftImageProductInclusion f g h i z w v
local notation3 (prettyPrint := false) "ι" =>
  correspondenceSupportProductInclusion f h i (correspondenceIncidenceMap f g h z w t) v

example (p : P) :
    RingHom.ker (correspondenceRemainingSupportImageStalkMap f g h i z w v t p) =
      IdealSheafData.stalk D (correspondenceRemainingSupportImagePoint f g h i z w v t p) :=
  correspondenceRemainingSupportToImageExterior_stalkMap_ker f g h i z w v t p

example (p : P) :
    let q := correspondenceRemainingSupportImagePoint f g h i z w v t p
    let R := (T).presheaf.stalk q
    let B := (P).presheaf.stalk p
    let I : Ideal R := IdealSheafData.stalk D q
    let φ : R →+* B := correspondenceRemainingSupportImageStalkMap f g h i z w v t p
    letI : Algebra R B := φ.toAlgebra
    (R ⧸ I) ≃ₐ[R] B :=
  correspondenceRemainingImageComponentSupportStalkAlgEquiv f g h i z w v t p

example (p : P) {r : ℕ}
    (a : Fin r → (T).presheaf.stalk (correspondenceRemainingSupportImagePoint f g h i z w v t p))
    (n : ℕ) :
    let q := correspondenceRemainingSupportImagePoint f g h i z w v t p
    let R := (T).presheaf.stalk q
    let B := (P).presheaf.stalk p
    let I : Ideal R := IdealSheafData.stalk D q
    let φ : R →+* B := correspondenceRemainingSupportImageStalkMap f g h i z w v t p
    (Koszul.seqComplexTensor a (R ⧸ I)).homology n ≅
      (ModuleCat.restrictScalars φ).obj
        ((Koszul.seqComplexTensor (fun j => φ (a j)) B).homology n) :=
  correspondenceRemainingImageComponentSupportKoszulIso f g h i z w v t p a n

example (p : P) {r : ℕ}
    (a : Fin r → (T).presheaf.stalk (correspondenceRemainingSupportImagePoint f g h i z w v t p)) :
    let q := correspondenceRemainingSupportImagePoint f g h i z w v t p
    let R := (T).presheaf.stalk q
    let B := (P).presheaf.stalk p
    let I : Ideal R := IdealSheafData.stalk D q
    let φ : R →+* B := correspondenceRemainingSupportImageStalkMap f g h i z w v t p
    Koszul.seqEuler a (R ⧸ I) = Koszul.seqEuler (fun j => φ (a j)) B :=
  seqEuler_correspondenceRemainingImageComponentSupport f g h i z w v t p a

end Stacks.Chow
