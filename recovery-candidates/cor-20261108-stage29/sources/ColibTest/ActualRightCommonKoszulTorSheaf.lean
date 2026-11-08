/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RightCommonKoszulTorSheaf
import Colib.AlgebraicGeometry.Correspondences.Composition.TripleOriginalMiddleLists

/-! Consumers of the literal common Z list and full exterior multiplicity. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence Stacks.Chow
open AlgebraicGeometry.TorFormula
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : correspondenceTripleIncidence f g h i z w v)
  [Flat f] [Flat g] [Flat i] [IsSeparated h]
  [Flat (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)]

local notation3 (prettyPrint := false) "q" =>
  correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x
local notation3 (prettyPrint := false) "π" => correspondenceRightExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "p" =>
  correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
local notation3 (prettyPrint := false) "R₂" =>
  (pullback h h).presheaf.stalk (correspondenceSixfoldSecondMiddlePair f g h i p)
local notation3 (prettyPrint := false) "γ" =>
  ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
local notation3 (prettyPrint := false) "M" =>
  correspondenceTripleIncidenceSupportStalkModule f g h i z w v x
local notation3 (prettyPrint := false) "P" =>
  (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk q
local notation3 (prettyPrint := false) "P₀" =>
  (correspondenceIncidence g h i w v).presheaf.stalk (π q)

example (s : List R₂) (hs : IsRegular R₂ s)
    (hks : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
      Ideal.ofList (s.map γ)) (n : ℕ) :
    let l := s.map γ
    let hreg := correspondenceCommonSecondList_rightFirst_regular f g h i z w v x s hs hks
    letI := correspondenceTripleIncidenceRightFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    (Koszul.seqComplexTensor l.get M).homology n ≃ₗ[P]
      ((correspondenceRightExteriorTorSheaf f g h i z w v n).presheaf.stalk q) :=
  correspondenceTripleIncidenceRightCommonKoszulIsoTorSheaf f g h i z w v x s hs hks n

example (s : List R₂) (hs : IsRegular R₂ s)
    (hks : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
      Ideal.ofList (s.map γ)) (n : ℕ) :
    let l := s.map γ
    let hreg := correspondenceCommonSecondList_rightFirst_regular f g h i z w v x s hs hks
    letI := correspondenceTripleIncidenceRightFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    Module.length P ((Koszul.seqComplexTensor l.get M).homology n) =
      Module.length P ((correspondenceRightExteriorTorSheaf f g h i z w v n).presheaf.stalk q) :=
  length_correspondenceTripleIncidenceRightCommonKoszul_eq_torSheaf f g h i z w v x s hs hks n

example (s : List R₂) (hs : IsRegular R₂ s)
    (hks : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
      Ideal.ofList (s.map γ)) (n : ℕ) :
    let l := s.map γ
    let hreg := correspondenceCommonSecondList_rightFirst_regular f g h i z w v x s hs hks
    letI := correspondenceTripleIncidenceRightFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    letI := correspondenceIncidenceTorModule g h i w v (π q) n
    Module.length P ((Koszul.seqComplexTensor l.get M).homology n) =
      Module.length P₀ (correspondenceIncidenceAmbientTor g h i w v (π q) n) *
        Module.length P (P ⧸ (IsLocalRing.maximalIdeal P₀).map (π.stalkMap q).hom) :=
  length_correspondenceTripleIncidenceRightCommonKoszul_eq_mul f g h i z w v x s hs hks n

-- A real original-middle witness supplies the hypotheses, with one list for all degrees.
example [Smooth g] [IsSeparated g] [Smooth h] :
    ∃ (s : List R₂) (hs : IsRegular R₂ s)
      (hks : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
        Ideal.ofList (s.map γ)),
      ∀ n : ℕ,
        let l := s.map γ
        let hreg := correspondenceCommonSecondList_rightFirst_regular f g h i z w v x s hs hks
        letI := correspondenceTripleIncidenceRightFirstKoszulModule
          f g h i z w v x l hreg.1 hreg.2 n
        Nonempty ((Koszul.seqComplexTensor l.get M).homology n ≃ₗ[P]
          ((correspondenceRightExteriorTorSheaf f g h i z w v n).presheaf.stalk q)) := by
  obtain ⟨_, s, _, hs, _, hks⟩ := exists_correspondenceOriginalMiddleLists f g h i
    (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x)
  exact ⟨s, hs, hks, fun n =>
    ⟨correspondenceTripleIncidenceRightCommonKoszulIsoTorSheaf f g h i z w v x s hs hks n⟩⟩
