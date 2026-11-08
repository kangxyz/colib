module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingWeightedCycleEuler

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow TopologicalSpace
open RingTheory.Sequence

universe u

attribute [local instance 100000] HasDerivedCategory.standard


variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (hv : IsFiniteCorrespondencePoint h i v)
  (x : genericPoints (correspondenceLeftImageIncidence f g h i z w v))

local notation3 (prettyPrint := false) "R" =>
  correspondenceRemainingImageStalk f g h i z w v x.1
local notation3 (prettyPrint := false) "B" =>
  correspondenceRemainingFiniteRing f g h i z w v x.1
local notation3 (prettyPrint := false) "x₀" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v x.1
local notation3 (prettyPrint := false) "A" => (pullback h h).presheaf.stalk
  (correspondenceLeftImageMiddlePair f g h i z w v x₀)
local notation3 (prettyPrint := false) "α" =>
  correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1
local notation3 (prettyPrint := false) "M" =>
  correspondenceRemainingFiniteTorModule f g h i z w v x.1
local notation3 (prettyPrint := false) "sJ" => correspondenceIntermediateImageTarget f g h z w ≫ h
local notation3 (prettyPrint := false) "sV" =>
  (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)

include hz hw hv

example
    [LocallyOfFiniteType sJ] [LocallyOfFiniteType sV] {r : ℕ}
    (s : Fin r → A) (hsr : IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v x₀) = Ideal.span (Set.range s)) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
    ∑ᶠ b : ℕ, (-1 : ℤ) ^ b *
      Koszul.seqEuler (fun j => α (s j))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj (M b)) =
      correspondenceLeftWeightedRemainingCycle f g h i z w v hw hv x.1 :=
  finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_weightedCycle
    K f g h i z w v hz hw hv x s hsr hs

#check finsum_signed_seqEuler_correspondenceRemainingFiniteTorModule_weightedCycle
