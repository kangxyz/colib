/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageComponentIncidence

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i) (t : correspondenceIncidence f g h z w)

local notation3 (prettyPrint := false) "q" => correspondenceIncidenceMap f g h z w t
local notation3 (prettyPrint := false) "P" => correspondenceSupportProduct f h i q v
local notation3 (prettyPrint := false) "N" => correspondenceIncidence f h i q v
local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "L" => correspondenceLeftImageIncidence f g h i z w v
local notation3 (prettyPrint := false) "u" =>
  correspondenceRemainingSupportToImageExterior f g h i z w v t
local notation3 (prettyPrint := false) "a" => correspondenceIncidenceToSupportProduct f h i q v
local notation3 (prettyPrint := false) "b" => correspondenceIncidenceInclusion f h i q v
local notation3 (prettyPrint := false) "j" => correspondenceLeftImageProductInclusion f g h i z w v
local notation3 (prettyPrint := false) "ι" => correspondenceSupportProductInclusion f h i q v
local notation3 (prettyPrint := false) "d" => correspondenceTripleInclusion f h i
local notation3 (prettyPrint := false) "m" => correspondenceMiddlePair f h i
local notation3 (prettyPrint := false) "mT" => correspondenceLeftImageMiddlePair f g h i z w v
local notation3 (prettyPrint := false) "jL" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v
local notation3 (prettyPrint := false) "k" => correspondenceTripleMiddle f h i
local notation3 (prettyPrint := false) "kL" =>
  pullback.fst (correspondenceIntermediateImageTarget f g h z w)
    ((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫
      correspondenceIntermediateImageTarget f g h z w

example : IsPullback (correspondenceRemainingPairToImageIncidence f g h i z w v t)
    a jL u :=
  correspondenceRemainingPairToImageIncidence_isPullback f g h i z w v t

example (y : N) :
    jL (correspondenceRemainingPairToImageIncidence f g h i z w v t y) = u (a y) :=
  correspondenceRemainingPairToImageIncidence_point f g h i z w v t y

example (y : N)
    (hy : correspondenceRemainingPairToImageIncidence f g h i z w v t y ∈ genericPoints L) :
    y ∈ genericPoints N :=
  mem_genericPoints_correspondenceRemainingPair_of_image f g h i z w v t y hy

end Stacks.Chow
