/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightStageCommonMiddleList
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightFirstTorSheaf

/-!
# The common Z-first list realizes the actual right exterior Tor family

The list is the literal ordered original Z family supplied in the common
sixfold ambient, not an independently selected replacement. The preceding
module derives its original ideal and scalar transport and identifies first
homology with the actual G,H Tor tensor. This file composes that P-linear
comparison with the global right exterior Tor-sheaf stalk isomorphism.

The raw extended length also retains the full closed-fibre multiplicity.
Nothing is reduced, no fibre multiplicity is declared one, and there is no
conversion of an infinite length to a natural number. The common signed total
order comparison and weighted remaining bracket identity remain distinct.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence
open AlgebraicGeometry.TorFormula
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

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

/-- The literal common Z-first homology is the actual exterior sheaf stalk with its full action. -/
def correspondenceTripleIncidenceRightCommonKoszulIsoTorSheaf
    (s : List R₂) (hs : IsRegular R₂ s)
    (hks : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
      Ideal.ofList (s.map γ)) (n : ℕ) :
    let l := s.map γ
    let hreg := correspondenceCommonSecondList_rightFirst_regular f g h i z w v x s hs hks
    letI := correspondenceTripleIncidenceRightFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    (Koszul.seqComplexTensor l.get M).homology n ≃ₗ[P]
      ((correspondenceRightExteriorTorSheaf f g h i z w v n).presheaf.stalk q) := by
  let l := s.map γ
  let hreg := correspondenceCommonSecondList_rightFirst_regular f g h i z w v x s hs hks
  letI := correspondenceTripleIncidenceRightFirstKoszulModule
    f g h i z w v x l hreg.1 hreg.2 n
  exact (correspondenceTripleIncidenceRightCommonKoszulIsoOriginalPairTor
    f g h i z w v x s hs hks n).trans
      (correspondenceRightExteriorTorSheafStalkIso f g h i z w v q n).toLinearEquiv.symm

/-- Raw lengths are equal over the full right-stage stalk in every degree. -/
theorem length_correspondenceTripleIncidenceRightCommonKoszul_eq_torSheaf
    (s : List R₂) (hs : IsRegular R₂ s)
    (hks : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
      Ideal.ofList (s.map γ)) (n : ℕ) :
    let l := s.map γ
    let hreg := correspondenceCommonSecondList_rightFirst_regular f g h i z w v x s hs hks
    letI := correspondenceTripleIncidenceRightFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    Module.length P ((Koszul.seqComplexTensor l.get M).homology n) =
      Module.length P ((correspondenceRightExteriorTorSheaf f g h i z w v n).presheaf.stalk q) :=
  (correspondenceTripleIncidenceRightCommonKoszulIsoTorSheaf f g h i z w v x s hs hks n).length_eq

/-- The common first-homology length keeps the complete actual exterior closed-fibre factor. -/
theorem length_correspondenceTripleIncidenceRightCommonKoszul_eq_mul
    (s : List R₂) (hs : IsRegular R₂ s)
    (hks : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p =
      Ideal.ofList (s.map γ)) (n : ℕ) :
    let l := s.map γ
    let hreg := correspondenceCommonSecondList_rightFirst_regular f g h i z w v x s hs hks
    letI := correspondenceTripleIncidenceRightFirstKoszulModule
      f g h i z w v x l hreg.1 hreg.2 n
    letI := correspondenceIncidenceTorModule g h i w v (π q) n
    Module.length P ((Koszul.seqComplexTensor l.get M).homology n) =
      Module.length P₀ (correspondenceIncidenceAmbientTor g h i w v (π q) n) *
        Module.length P (P ⧸ (IsLocalRing.maximalIdeal P₀).map (π.stalkMap q).hom) := by
  exact (length_correspondenceTripleIncidenceRightCommonKoszul_eq_torSheaf
    f g h i z w v x s hs hks n).trans
      (length_correspondenceRightExteriorTorSheaf_eq_mul f g h i z w v q n)

end Stacks.Chow
