module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageComponentGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (t : correspondenceIncidence f g h z w)

local notation3 (prettyPrint := false) "r" => correspondenceIncidenceMap f g h z w
local notation3 (prettyPrint := false) "J" => correspondenceIntermediateImage f g h z w
local notation3 (prettyPrint := false) "F" => integralComponentAt ((r).toImage t)
local notation3 (prettyPrint := false) "G" => integralComponentAt (r t)
local notation3 (prettyPrint := false) "V" => integralComponentAt v
local notation3 (prettyPrint := false) "sJ" => correspondenceIntermediateImageTarget f g h z w ≫ h
local notation3 (prettyPrint := false) "sV" => ((V).subschemeι ≫ pullback.fst h i) ≫ h
local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "π'" =>
  correspondenceLeftImageExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "D" => correspondenceRemainingImageComponent f g h i z w v t
local notation3 (prettyPrint := false) "P" => correspondenceSupportProduct f h i (r t) v
local notation3 (prettyPrint := false) "j" => correspondenceLeftImageProductInclusion f g h i z w v
local notation3 (prettyPrint := false) "ι" => correspondenceSupportProductInclusion f h i (r t) v


example :
    ∃ e : (F).subscheme ≅ (G).subscheme,
      e.hom ≫ (G).subschemeι = (F).subschemeι ≫ (r).imageι :=
  exists_correspondenceRemainingImagePointIso f g h z w t

example :
    ∃ e : (D).subscheme ≅ P, e.hom ≫ ι = (D).subschemeι ≫ j :=
  exists_correspondenceRemainingImageComponentSupportIso f g h i z w v t

#check exists_correspondenceRemainingImagePointIso
#check exists_correspondenceRemainingImageComponentSupportIso
