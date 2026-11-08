/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleLeftColumnTor
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightStageCommonMiddleList

/-!
# The original Y and Z lists give the actual left column comparison

This consumer retains the exact original-middle lists and their ordered images.
It reuses the existing common-Z regularity supplier from the right-stage owner;
no second provider or replacement regular list is introduced. The module map is
the actual quotient-action/Koszul restriction comparison of `TripleLeftColumnTor`.
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

variable [Flat f] [Flat g] [Flat h] [Flat i] [IsSeparated h]

/-- The actual left column for the unchanged original Y and Z lists, with the
canonical first-stage action from their real pulled-back diagonal equations. -/
def correspondenceOriginalMiddleListsLeftTorIsoRemainingKoszul
    (t : List ((pullback g g).presheaf.stalk
      (correspondenceSixfoldFirstMiddlePair f g h i p)))
    (s : List ((pullback h h).presheaf.stalk
      (correspondenceSixfoldSecondMiddlePair f g h i p)))
    (ht : IsRegular ((pullback g g).presheaf.stalk
      (correspondenceSixfoldFirstMiddlePair f g h i p)) t)
    (hs : IsRegular ((pullback h h).presheaf.stalk
      (correspondenceSixfoldSecondMiddlePair f g h i p)) s)
    (hY : IY = Ideal.ofList
      (t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom))
    (hZ : IZ = Ideal.ofList
      (s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom)) (a b : ℕ) :
    let t' := t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom
    let s' := s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom
    let hr := correspondenceOriginalMiddleLists_regular_append f g h i
      (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x) t s ht hs hY hZ
    correspondenceTripleIncidenceLeftIteratedTor f g h i z w v x a b ≅
      (ModuleCat.restrictScalars φ).obj
        ((Koszul.seqComplexTensor (fun j => φ (s'.get j))
          (correspondenceRemainingFirstKoszulModule
            f g h i z w v x t' hr.1 hY b)).homology a) := by
  dsimp only
  exact correspondenceTripleIncidenceLeftIteratedTorIsoRemainingKoszul f g h i z w v x _ _
    (correspondenceOriginalMiddleLists_regular_append f g h i
      (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v x) t s ht hs hY hZ).1
    (correspondenceCommonSecondList_rightFirst_regular f g h i z w v x s hs hZ).1 hY hZ a b

end Stacks.Chow
