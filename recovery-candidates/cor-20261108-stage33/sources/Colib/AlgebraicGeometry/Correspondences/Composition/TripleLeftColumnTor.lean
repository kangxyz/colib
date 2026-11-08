/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleIteratedTorComparison
public import Colib.RingTheory.Koszul.RestrictionComparison
public import StacksFrontier.RingTheory.Koszul.Localization

/-!
# The actual left Tor column is remaining Koszul homology over the first-stage stalk

The first Koszul homology has the already proved action of the full first-stage
incidence-times-support stalk. Restriction of that action recovers its original
sixfold action by the exact scalar equation, not an assumed comparison. Native
quotient Tor, coefficient functoriality, and the arbitrary-ring-map Koszul
projection formula identify each iterated Tor degree with remaining homology over
that actual first-stage ring. The original quotient map is surjective, so the
comparison preserves full module length, including before integer conversion.

The separate original-middle-list consumer uses the same Y and Z stalk lists selected
in `TripleOriginalMiddleLists`, pulled by the original sixfold projections. Neither
regularity of the full exterior support nor flatness of a finite image map is
required. This is a local column comparison; global finite-algebra localization
and residue-degree assembly are distinct obligations.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [IsSeparated g]
  (x : correspondenceTripleIncidence f g h i z w v)

local notation3 (prettyPrint := false) "A" =>
  correspondenceTripleIncidenceAmbientStalk f g h i z w v x
local notation3 (prettyPrint := false) "P" =>
  correspondenceRemainingOriginalStalk f g h i z w v x
local notation3 (prettyPrint := false) "M" =>
  correspondenceTripleIncidenceSupportStalkModule f g h i z w v x
local notation3 (prettyPrint := false) "φ" =>
  correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x
local notation3 (prettyPrint := false) "p" =>
  correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
local notation3 (prettyPrint := false) "IY" =>
  IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p
local notation3 (prettyPrint := false) "IZ" =>
  IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p

/-- The already constructed first-stage action restricts to exactly the original
sixfold action on first Koszul homology. The carrier map is the identity. -/
def correspondenceTripleIncidenceFirstKoszulRestrictIso
    (t : List A) (ht : IsRegular A t) (hY : IY = Ideal.ofList t) (b : ℕ) :
    (Koszul.seqComplexTensor t.get M).homology b ≅
      (ModuleCat.restrictScalars φ).obj
        (correspondenceRemainingFirstKoszulModule f g h i z w v x t ht hY b) := by
  let H := (Koszul.seqComplexTensor t.get M).homology b
  letI := correspondenceTripleIncidenceFirstKoszulModule f g h i z w v x t ht hY b
  apply LinearEquiv.toModuleIso
  refine { AddEquiv.refl H with map_smul' := ?_ }
  intro a m
  exact (correspondenceTripleIncidenceFirstKoszulModule_stalkMap_smul
    f g h i z w v x t ht hY b a m).symm

/-- Each actual iterated Tor module is the actual remaining Koszul homology,
restricted along the original surjective first-stage stalk map. -/
def correspondenceTripleIncidenceLeftIteratedTorIsoRemainingKoszul
    (t s : List A) (ht : IsRegular A t) (hs : IsRegular A s)
    (hY : IY = Ideal.ofList t) (hZ : IZ = Ideal.ofList s) (a b : ℕ) :
    correspondenceTripleIncidenceLeftIteratedTor f g h i z w v x a b ≅
      (ModuleCat.restrictScalars φ).obj
        ((Koszul.seqComplexTensor (fun j => φ (s.get j))
          (correspondenceRemainingFirstKoszulModule f g h i z w v x t ht hY b)).homology a) := by
  letI : Algebra A P := (φ).toAlgebra
  let H := (Koszul.seqComplexTensor t.get M).homology b
  let HP := correspondenceRemainingFirstKoszulModule f g h i z w v x t ht hY b
  let eY := Koszul.torIsoHomologySeqComplexTensorOfIsRegular t.get
    (by simpa only [List.ofFn_get] using ht) IY
    (hY.trans (by rw [← Ideal.ofList_ofFn, List.ofFn_get])) M b
  let eZ := Koszul.torIsoHomologySeqComplexTensorOfIsRegular s.get
    (by simpa only [List.ofFn_get] using hs) IZ
    (hZ.trans (by rw [← Ideal.ofList_ofFn, List.ofFn_get])) H a
  exact ((Tor (ModuleCat A) a).obj
      (correspondenceTripleIncidenceSecondDiagonalQuotient f g h i z w v x)).mapIso eY ≪≫
    eZ ≪≫ Koszul.homologyTensorCongr s.get
      (correspondenceTripleIncidenceFirstKoszulRestrictIso
        f g h i z w v x t ht hY b).toLinearEquiv a ≪≫
      Koszul.homologySeqComplexTensorRestrictScalarsIso s.get HP a

/-- Length is preserved over the actual first-stage ring, not merely after a support reduction. -/
theorem length_correspondenceTripleIncidenceLeftIteratedTor_eq_remainingKoszul
    (t s : List A) (ht : IsRegular A t) (hs : IsRegular A s)
    (hY : IY = Ideal.ofList t) (hZ : IZ = Ideal.ofList s) (a b : ℕ) :
    Module.length A (correspondenceTripleIncidenceLeftIteratedTor f g h i z w v x a b) =
      Module.length P ((Koszul.seqComplexTensor (fun j => φ (s.get j))
        (correspondenceRemainingFirstKoszulModule f g h i z w v x t ht hY b)).homology a) := by
  letI : Algebra A P := (φ).toAlgebra
  let H := (Koszul.seqComplexTensor (fun j => φ (s.get j))
    (correspondenceRemainingFirstKoszulModule f g h i z w v x t ht hY b)).homology a
  letI : Module A H := Module.compHom H φ
  have : IsScalarTower A P H := IsScalarTower.of_compHom A P H
  exact (correspondenceTripleIncidenceLeftIteratedTorIsoRemainingKoszul
    f g h i z w v x t s ht hs hY hZ a b).toLinearEquiv.length_eq.trans
      (Module.length_eq_of_surjective (M := H)
        (correspondenceTripleIncidenceFirstStageStalkMap_surjective f g h i z w v x))

end Stacks.Chow
