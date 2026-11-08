/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.FirstStageAmbientStalkSquare

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

variable (x : correspondenceTripleIncidence f g h i z w v)

local notation3 "u" => correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x
local notation3 "π" =>
  (pullback.fst (correspondenceIncidenceRight f g h z w ≫ h)
    (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h))
local notation3 "p" => correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
local notation3 "p₀" => correspondenceIncidenceAmbientInclusion f g h z w (π u)
local notation3 "e" => correspondenceTripleIncidenceToTripleSupport f g h i z w v x
local notation3 "e₀" => correspondenceIncidenceToSupportProduct f g h z w (π u)
local notation3 "A" => correspondenceTripleIncidenceAmbientStalk f g h i z w v x
local notation3 "A₀" => correspondenceIncidenceAmbientStalk f g h z w (π u)
local notation3 "D" => (correspondenceTripleSupportProduct f g h i z w v).presheaf.stalk e

example :
    (correspondenceTripleIncidenceSupportStalkMap f g h i z w v x).comp
        (correspondenceTripleIncidencePairAmbientStalkMap f g h i z w v x) =
      (correspondenceLeftExteriorSupportStalkMap f g h i z w v u).comp
        (correspondenceIncidenceSupportStalkMap f g h z w (π u)) :=
  correspondenceTripleIncidence_ambientSupport_stalk_comm f g h i z w v x

example :
    (((correspondenceLeftIntermediateToTripleSupport f g h i z w v).stalkMap u).hom).comp
        (correspondenceTripleIncidenceSupportStalkMap f g h i z w v x) =
      correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x :=
  correspondenceTripleIncidenceSupportStalkMap_firstStage_comp f g h i z w v x
