module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageComponentEuler

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "π'" =>
  correspondenceLeftImageExteriorProjection f g h i z w v

variable (x : correspondenceLeftImageIncidence f g h i z w v)
  (t : correspondenceIncidence f g h z w)

local notation3 (prettyPrint := false) "x₀" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v x
local notation3 (prettyPrint := false) "R" => correspondenceRemainingImageStalk f g h i z w v x
local notation3 (prettyPrint := false) "D" => correspondenceRemainingImageComponent f g h i z w v t
local notation3 (prettyPrint := false) "I" => IdealSheafData.stalk D x₀


open Classical in
example
    [IsLocallyNoetherian T]
    (p : {p : PrimeSpectrum R // IsMin p}) (hp : I ≤ p.1.asIdeal) :
    Module.length (Localization.AtPrime p.1.asIdeal)
      (LocalizedModule p.1.asIdeal.primeCompl
        (correspondenceRemainingImageComponentStalk f g h i z w v x t)) ≠ ⊤ :=
  length_correspondenceRemainingImageComponentStalk_ne_top f g h i z w v x t p hp

open Classical in
example
    [IsSeparated h] [IsLocallyNoetherian T]
    (hx : x ∈ genericPoints (correspondenceLeftImageIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → (pullback h h).presheaf.stalk
      (correspondenceLeftImageMiddlePair f g h i z w v x₀))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v x₀) = Ideal.span (Set.range s)) :
    Koszul.seqEuler
      (fun j => correspondenceRemainingImageMiddleStalkMap f g h i z w v x (s j))
      (correspondenceRemainingImageComponentStalk f g h i z w v x t) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        if hp : I ≤ p.1.asIdeal then
          componentMultiplicity (D).subschemeι
            (correspondenceRemainingImageComponentGenericLabel f g h i z w v x t p hp) *
              Koszul.seqEuler
                (fun j => correspondenceRemainingImageMiddleStalkMap f g h i z w v x (s j))
                (R ⧸ p.1.asIdeal)
        else 0 :=
  seqEuler_correspondenceRemainingImageComponentStalk f g h i z w v x t hx s hs

#check correspondenceRemainingImageComponent
#check correspondenceRemainingImageComponentStalk
#check exists_correspondenceRemainingImageComponentGenericLabel
#check correspondenceRemainingImageComponentGenericLabel
#check correspondenceRemainingImageComponentGenericLabel_spec
#check length_correspondenceRemainingImageComponentStalk_eq_componentMultiplicity
#check length_correspondenceRemainingImageComponentStalk_ne_top
#check seqEuler_correspondenceRemainingImageComponentStalk
