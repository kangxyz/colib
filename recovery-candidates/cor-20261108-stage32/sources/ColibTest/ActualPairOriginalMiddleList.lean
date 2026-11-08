/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.PairOriginalMiddleList

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence Stacks.Chow

universe u

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (x : correspondenceIncidence f g h z w)

local notation3 (prettyPrint := false) "p" => correspondenceIncidenceAmbientInclusion f g h z w x
local notation3 (prettyPrint := false) "m" => correspondenceMiddlePair f g h p
local notation3 (prettyPrint := false) "R" => (pullback g g).presheaf.stalk m
local notation3 (prettyPrint := false) "D" =>
  (correspondenceSupportProduct f g h z w).presheaf.stalk
    (correspondenceIncidenceToSupportProduct f g h z w x)
local notation3 (prettyPrint := false) "β" => ((correspondenceMiddlePair f g h).stalkMap p).hom
local notation3 (prettyPrint := false) "ρ" => correspondenceIncidenceSupportStalkMap f g h z w x

example [Smooth g] [IsSeparated g] :
    ∃ (r : ℕ) (t : Fin r → R), IsRegular R (List.ofFn t) ∧
      IdealSheafData.stalk (pullback.diagonal g).ker m = Ideal.span (Set.range t) :=
  exists_correspondenceIncidenceOriginalMiddleList f g h z w x

example [Flat f] [Smooth g] [IsSeparated g] [Flat h] :
    ∃ (r : ℕ) (t : Fin r → R), IsRegular R (List.ofFn t) ∧
      IdealSheafData.stalk (pullback.diagonal g).ker m = Ideal.span (Set.range t) ∧
      ∀ n : ℕ,
        letI := correspondenceIncidenceTorSupportModule f g h z w x n
        Nonempty (correspondenceIncidenceAmbientTor f g h z w x n ≃ₗ[D]
          ((Koszul.seqComplexTensor (fun j => ρ (β (t j))) D).homology n)) :=
  exists_correspondenceIncidenceOriginalMiddleList_tor f g h z w x
