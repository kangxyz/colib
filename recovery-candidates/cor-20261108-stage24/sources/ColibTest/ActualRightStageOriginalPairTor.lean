/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RightStageOriginalPairTor

/-! Consumers of the actual support scalar square and full right-stage linear comparison. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence Stacks.Chow
open scoped TensorProduct

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : correspondenceTripleIncidence f g h i z w v)
  [Flat f] [Flat g] [Flat i] [IsSeparated h]
  [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]

local notation3 (prettyPrint := false) "q" =>
  correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x
local notation3 (prettyPrint := false) "π" =>
  correspondenceRightExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "P" =>
  (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q
local notation3 (prettyPrint := false) "p₀" =>
  correspondenceIncidenceAmbientInclusion g h i w v (π q)
local notation3 (prettyPrint := false) "R₀" =>
  (pullback h h).presheaf.stalk (correspondenceMiddlePair g h i p₀)
local notation3 (prettyPrint := false) "β" =>
  ((correspondenceMiddlePair g h i).stalkMap p₀).hom
local notation3 (prettyPrint := false) "α" =>
  correspondenceTripleIncidenceRightPairAmbientStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "M" =>
  correspondenceTripleIncidenceSupportStalkModule f g h i z w v x


local notation3 (prettyPrint := false) "A" =>
  correspondenceTripleIncidenceAmbientStalk f g h i z w v x
local notation3 (prettyPrint := false) "D" =>
  (correspondenceTripleSupportProduct f g h i z w v).presheaf.stalk
    (correspondenceRightIntermediateToTripleSupport f g h i z w v q)
local notation3 (prettyPrint := false) "ε" =>
  correspondenceTripleIncidenceRightSupportStalkMap f g h i z w v x

-- This is the unchanged original common support module, with its actual point transport.
example : M ≅ (ModuleCat.restrictScalars ε).obj (ModuleCat.of D D) :=
  correspondenceTripleIncidenceRightSupportStalkIso f g h i z w v x

example : ε.comp α =
    (correspondenceRightExteriorSupportStalkMap f g h i z w v q).comp
      (correspondenceIncidenceSupportStalkMap g h i w v (π q)) :=
  correspondenceTripleIncidence_rightAmbientSupport_stalk_comm f g h i z w v x

example : (((correspondenceRightIntermediateToTripleSupport f g h i z w v).stalkMap q).hom).comp ε =
    correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x :=
  correspondenceTripleIncidenceRightSupportStalkMap_firstStage_comp f g h i z w v x

example : correspondenceMiddlePair g h i p₀ = correspondenceSixfoldSecondMiddlePair f g h i
    (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x) :=
  correspondenceTripleIncidence_originalSecondMiddle_point_eq f g h i z w v x

example : RingHom.ker (correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x) =
    correspondenceTripleIncidenceRightFirstStageStalkIdeal f g h i z w v x :=
  correspondenceTripleIncidenceRightFirstStageStalkMap_ker f g h i z w v x

-- Every homological degree, with both actual incidence actions retained.
example {r : ℕ} (s : Fin r → R₀) (hs : IsRegular R₀ (List.ofFn s))
    (hks : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceMiddlePair g h i p₀) = Ideal.span (Set.range s)) (n : ℕ) :
    let l := List.ofFn (fun j => α (β (s j)))
    let hreg := correspondenceOriginalLastPairList_rightFirst_regular f g h i z w v x s hs hks
    letI := correspondenceTripleIncidenceRightFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    let P₀ := (correspondenceIncidence g h i w v).presheaf.stalk (π q)
    letI := correspondenceIncidenceTorModule g h i w v (π q) n
    letI : Algebra P₀ P := (π.stalkMap q).hom.toAlgebra
    (Koszul.seqComplexTensor l.get M).homology n ≃ₗ[P]
      (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π q) n) :=
  correspondenceTripleIncidenceRightFirstKoszulIsoOriginalPairTor f g h i z w v x s hs hks n
