/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RightStageCommonMiddleList

/-! Exact-list, original-ideal, and full scalar-action consumers. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence Stacks.Chow
open scoped TensorProduct

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

variable (x : correspondenceTripleIncidence f g h i z w v)

local notation3 (prettyPrint := false) "q" =>
  correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x
local notation3 (prettyPrint := false) "π" => correspondenceRightExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "p" =>
  correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
local notation3 (prettyPrint := false) "p₀" =>
  correspondenceIncidenceAmbientInclusion g h i w v (π q)
local notation3 (prettyPrint := false) "A" => correspondenceTripleIncidenceAmbientStalk f g h i z w v x
local notation3 (prettyPrint := false) "R₀" =>
  (pullback h h).presheaf.stalk (correspondenceMiddlePair g h i p₀)
local notation3 (prettyPrint := false) "R₂" =>
  (pullback h h).presheaf.stalk (correspondenceSixfoldSecondMiddlePair f g h i p)
local notation3 (prettyPrint := false) "σ" =>
  (pullback h h).presheaf.stalkCongr (Inseparable.of_eq
    (correspondenceTripleIncidence_originalSecondMiddle_point_eq f g h i z w v x))
local notation3 (prettyPrint := false) "α" =>
  correspondenceTripleIncidenceRightPairAmbientStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "β" => ((correspondenceMiddlePair g h i).stalkMap p₀).hom
local notation3 (prettyPrint := false) "γ" =>
  ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
local notation3 (prettyPrint := false) "M" =>
  correspondenceTripleIncidenceSupportStalkModule f g h i z w v x
local notation3 (prettyPrint := false) "P" =>
  (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q
local notation3 (prettyPrint := false) "P₀" =>
  (correspondenceIncidence g h i w v).presheaf.stalk (π q)
local notation3 (prettyPrint := false) "κ" =>
  correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x

example (s : List R₂) :
    (correspondenceRightOriginalMiddleList f g h i z w v x s).map (α.comp β) = s.map γ :=
  correspondenceRightOriginalMiddleList_map f g h i z w v x s

example [Flat f] [Flat g] [Flat i] [IsSeparated h] (s : List R₂)
    (hks : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
      Ideal.ofList (s.map γ)) :
    IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceSixfoldSecondMiddlePair f g h i p) = Ideal.ofList s :=
  correspondenceCommonSecondList_diagonalIdeal f g h i z w v x s hks

example [Flat f] [Flat g] [Flat i] [IsSeparated h] (s : List R₂) (hs : IsRegular R₂ s)
    (hks : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
      Ideal.ofList (s.map γ)) :
    IsRegular R₀ (correspondenceRightOriginalMiddleList f g h i z w v x s) ∧
      IdealSheafData.stalk (pullback.diagonal h).ker (correspondenceMiddlePair g h i p₀) =
        Ideal.ofList (correspondenceRightOriginalMiddleList f g h i z w v x s) :=
  correspondenceRightOriginalMiddleList_regular_ideal f g h i z w v x s hs hks

example [Flat f] [Flat g] [Flat i] (s : List R₂) (hs : IsRegular R₂ s)
    (hks : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
      Ideal.ofList (s.map γ)) :
    IsRegular A (s.map γ) ∧
      IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
        Ideal.ofList (s.map γ) :=
  correspondenceCommonSecondList_rightFirst_regular f g h i z w v x s hs hks

example [Flat f] [Flat g] [Flat i] [IsSeparated h]
    [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]
    (s : List R₂) (hs : IsRegular R₂ s)
    (hks : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
      Ideal.ofList (s.map γ)) (n : ℕ) :
    let l := s.map γ
    let hreg := correspondenceCommonSecondList_rightFirst_regular f g h i z w v x s hs hks
    letI := correspondenceTripleIncidenceRightFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    letI := correspondenceIncidenceTorModule g h i w v (π q) n
    letI : Algebra P₀ P := (π.stalkMap q).hom.toAlgebra
    (Koszul.seqComplexTensor l.get M).homology n ≃ₗ[P]
      (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π q) n) :=
  correspondenceTripleIncidenceRightCommonKoszulIsoOriginalPairTor f g h i z w v x s hs hks n

-- No perfect-field, geometric-integrality, or connectedness restriction.
example (k : Type u) [Field k]
    (f' : X ⟶ Spec (.of k)) (g' : Y ⟶ Spec (.of k))
    (h' : Z ⟶ Spec (.of k)) (i' : W ⟶ Spec (.of k)) :
    Flat (correspondenceSixfoldSecondMiddlePair f' g' h' i') := inferInstance
