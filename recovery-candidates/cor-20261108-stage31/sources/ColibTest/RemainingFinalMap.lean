module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFinalMap

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u


variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

local notation3 (prettyPrint := false) "L" => correspondenceLeftImageIncidence f g h i z w v
local notation3 (prettyPrint := false) "r" => correspondenceIncidenceMap f g h z w
local notation3 (prettyPrint := false) "V" => integralComponentAt v
local notation3 (prettyPrint := false) "C" => correspondenceIntermediateImageTarget f g h z w
local notation3 (prettyPrint := false) "B" => (V).subschemeι ≫ pullback.fst h i

example
    [IsSeparated h] [LocallyOfFiniteType h] [IsSeparated i]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v) :
    IsFinite (correspondenceLeftImageIncidenceMap f g h i z w v) :=
  isFinite_correspondenceLeftImageIncidenceMap
    f g h i z w v hz hw hv

example [IsSeparated h]
    (t : correspondenceIncidence f g h z w) :
    correspondenceRemainingPairToImageIncidence f g h i z w v t ≫
        correspondenceLeftImageIncidenceMap f g h i z w v =
      correspondenceIncidenceMap f h i (r t) v :=
  correspondenceRemainingPairToImageIncidence_map
    f g h i z w v t

example :
    correspondenceTripleToLeftImageIncidence f g h i z w v ≫
        correspondenceLeftImageIncidenceMap f g h i z w v =
      correspondenceTripleIncidenceMap f g h i z w v :=
  correspondenceTripleToLeftImageIncidence_map
    f g h i z w v

#check correspondenceLeftImageIncidenceToTripleProduct
#check correspondenceLeftImageIncidenceToTripleProduct_ambient
#check correspondenceLeftImageIncidenceSource
#check correspondenceLeftImageIncidenceTarget
#check correspondenceLeftImageIncidenceMap
#check correspondenceLeftImageIncidenceMap_fst
#check correspondenceLeftImageIncidenceMap_snd
#check isFinite_correspondenceLeftImageIncidenceSource
#check isFinite_correspondenceLeftImageIncidenceMap
#check correspondenceRemainingPairToImageIncidence_triple
#check correspondenceRemainingPairToImageIncidence_map
#check correspondenceTripleToLeftImageIncidence_map
#check correspondenceLeftImageIncidenceToTripleProduct_ambient_assoc
#check correspondenceLeftImageIncidenceMap_fst_assoc
#check correspondenceLeftImageIncidenceMap_snd_assoc
#check correspondenceRemainingPairToImageIncidence_triple_assoc
#check correspondenceRemainingPairToImageIncidence_map_assoc
#check correspondenceTripleToLeftImageIncidence_map_assoc
