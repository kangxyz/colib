module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFixedLabelEuler

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

local notation3 (prettyPrint := false) "E" =>
  correspondenceLeftIntermediateSupportProduct f g h i z w v
local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "q" => (correspondenceIncidenceMap f g h z w).toImage
local notation3 (prettyPrint := false) "q'" =>
  correspondenceLeftIntermediateImageMap f g h i z w v
local notation3 (prettyPrint := false) "π" => correspondenceLeftExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "π'" =>
  correspondenceLeftImageExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "sJ" => correspondenceIntermediateImageTarget f g h z w ≫ h
local notation3 (prettyPrint := false) "sV" =>
  (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)

variable (x : correspondenceLeftImageIncidence f g h i z w v)
  (t : correspondenceIncidence f g h z w)

local notation3 (prettyPrint := false) "x₀" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v x
local notation3 (prettyPrint := false) "R" => correspondenceRemainingImageStalk f g h i z w v x
local notation3 (prettyPrint := false) "D" => correspondenceRemainingImageComponent f g h i z w v t
local notation3 (prettyPrint := false) "I" => IdealSheafData.stalk D x₀
local notation3 (prettyPrint := false) "α" =>
  correspondenceRemainingImageMiddleStalkMap f g h i z w v x


open Classical in
example
    (p : {p : PrimeSpectrum R // IsMin p}) :
    I ≤ p.1.asIdeal ↔ π' ((T).fromSpecStalk x₀ p.1) = q t :=
  correspondenceRemainingImageComponent_stalk_le_iff_projection K f g h i z w v x t p

open Classical in
example
    [IsSeparated h] [LocallyOfFiniteType sJ] [LocallyOfFiniteType sV]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hx : x ∈ genericPoints (correspondenceLeftImageIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → (pullback h h).presheaf.stalk
      (correspondenceLeftImageMiddlePair f g h i z w v x₀))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v x₀) = Ideal.span (Set.range s)) :
    ((q).residueDegree t : ℤ) * Koszul.seqEuler (fun j => α (s j))
      (correspondenceRemainingImageComponentStalk f g h i z w v x t) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        (∑ᶠ η : {η : genericPoints E // q' η.1 = (T).fromSpecStalk x₀ p.1},
          if π η.1.1 = t then
            (correspondenceLeftExteriorFiberLength f g h i z w v η.1.1 : ℤ) *
              ((q').residueDegree η.1.1 : ℤ)
          else 0) * Koszul.seqEuler (fun j => α (s j)) (R ⧸ p.1.asIdeal) :=
  residueDegree_mul_seqEuler_correspondenceRemainingImageComponentStalk
    K f g h i z w v x t hz hw hx s hs

#check correspondenceRemainingImageComponent_stalk_le_iff_projection
#check residueDegree_mul_seqEuler_correspondenceRemainingImageComponentStalk
