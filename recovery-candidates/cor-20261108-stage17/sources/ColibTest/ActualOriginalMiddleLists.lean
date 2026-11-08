/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.TripleOriginalMiddleLists

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  [Flat f] [Smooth g] [IsSeparated g] [Smooth h] [IsSeparated h] [Flat i]

example (q : correspondenceFourfoldProduct f g h i) :
    let p := correspondenceFourfoldDiagonalInclusion f g h i q
    ∃ (t : List ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)))
      (s : List ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p))),
      RingTheory.Sequence.IsRegular ((correspondenceSixfoldAmbient f g h i).presheaf.stalk p)
        (t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom ++
          s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom) := by
  dsimp only
  obtain ⟨t, s, ht, hs, hkt, hks⟩ := exists_correspondenceOriginalMiddleLists f g h i q
  exact ⟨t, s, (correspondenceOriginalMiddleLists_regular_append
    f g h i q t s ht hs hkt hks).2.2.2.1⟩

example (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
    (v : pullback (C := Scheme) h i)
    (x : correspondenceTripleIncidence f g h i z w v) :
    let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
    ∃ (t : List ((pullback g g).presheaf.stalk
        (correspondenceSixfoldFirstMiddlePair f g h i p)))
      (s : List ((pullback h h).presheaf.stalk
        (correspondenceSixfoldSecondMiddlePair f g h i p))),
      ∀ n : ℕ, Nonempty (correspondenceTripleIncidenceTor f g h i z w v x n ≅
        (correspondenceTripleIncidenceTwoListTotal f g h i z w v x
          (t.map ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap p).hom)
        (s.map ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap p).hom)).homology n) := by
  dsimp only
  obtain ⟨t, s, _, _, _, _, hiso⟩ :=
    exists_correspondenceOriginalMiddleLists_tor_iso f g h i z w v x
  exact ⟨t, s, hiso⟩
