/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.FirstTorImageCycleBaseChange

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

local notation3 (prettyPrint := false) "C" => fieldChowSituation K
local notation3 (prettyPrint := false) "I" => correspondenceIncidence f g h z w
local notation3 (prettyPrint := false) "J" => correspondenceIntermediateImage f g h z w
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
local notation3 (prettyPrint := false) "sI" => q ≫ sJ
local notation3 (prettyPrint := false) "sE" => π ≫ sI
local notation3 (prettyPrint := false) "sT" => π' ≫ sJ

example [LocallyOfFiniteType sV] :
    ∃ r : ℕ, AlgebraicGeometry.RelativeDimension π' r :=
  ⟨correspondenceThirdSupportDimension K h i v,
    relativeDimension_correspondenceLeftImageExteriorProjection K f g h i z w v⟩

open Classical in
example [IsSeparated h] [LocallyOfFiniteType sJ] [LocallyOfFiniteType sV]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (t : I) (p : T) (hp : π' p = q t) :
    letI := isFinite_correspondenceIncidenceToImage f g h z w hz hw
    letI := isFinite_correspondenceLeftIntermediateImageMap f g h i z w v hz hw
    let d := relativeDimension (C).dimensionFunction sI t
    let r := correspondenceThirdSupportDimension K h i v
    ((q).residueDegree t : ℤ) * flatPullbackWeight C sT π' (d + (r : ℤ)) p =
      ∑ᶠ η ∈ (q').base ⁻¹' {p},
        if π η = t then
          flatPullbackWeight C sE π (d + (r : ℤ)) η * ((q').residueDegree η : ℤ)
        else 0 :=
  correspondenceLeftImage_fixedLabel_pushPull K f g h i z w v hz hw t p hp

end Stacks.Chow
