/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageComponentStalk

noncomputable section

set_option backward.isDefEq.respectTransparency false

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

variable (p : P)

local notation3 (prettyPrint := false) "u" =>
  correspondenceRemainingSupportToImageExterior f g h i z w v t
local notation3 (prettyPrint := false) "R" => (T).presheaf.stalk (u p)
local notation3 (prettyPrint := false) "B" => (P).presheaf.stalk p
local notation3 (prettyPrint := false) "I" => IdealSheafData.stalk D (u p)
local notation3 (prettyPrint := false) "φ" => ((u).stalkMap p).hom

example : RingHom.ker φ = I :=
  correspondenceRemainingSupportToImageExterior_stalkMap_ker f g h i z w v t p

example : letI : Algebra R B := (φ).toAlgebra; (R ⧸ I) ≃ₐ[R] B :=
  correspondenceRemainingImageComponentSupportStalkAlgEquiv f g h i z w v t p

example {r : ℕ} (a : Fin r → R) (n : ℕ) :
    (Koszul.seqComplexTensor a (R ⧸ I)).homology n ≅
      (ModuleCat.restrictScalars φ).obj
        ((Koszul.seqComplexTensor (fun j => φ (a j)) B).homology n) :=
  correspondenceRemainingImageComponentSupportKoszulIso f g h i z w v t p a n

example {r : ℕ} (a : Fin r → R) :
    Koszul.seqEuler a (R ⧸ I) = Koszul.seqEuler (fun j => φ (a j)) B :=
  seqEuler_correspondenceRemainingImageComponentSupport f g h i z w v t p a

end Stacks.Chow
