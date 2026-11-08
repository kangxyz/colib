module

import Colib.AlgebraicGeometry.Correspondences.Composition.TripleColumnEulerComparison

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence TopologicalSpace
open scoped BigOperators

universe u

namespace Stacks.Chow

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (h : Z ⟶ Spec (.of k)) (i : W ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [Smooth h] [Smooth i] [IsSeparated g] [IsSeparated h]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : genericPoints (correspondenceTripleIncidence f g h i z w v))

local notation3 (prettyPrint := false) "A" =>
  correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1
local notation3 (prettyPrint := false) "φ" =>
  correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x.1
local notation3 (prettyPrint := false) "κ" =>
  correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x.1
local notation3 (prettyPrint := false) "p" =>
  correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1
local notation3 (prettyPrint := false) "IY" =>
  IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p
local notation3 (prettyPrint := false) "IZ" =>
  IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p

example
    (t s : List A) (ht : IsRegular A t) (hs : IsRegular A s)
    (hY : IY = Ideal.ofList t) (hZ : IZ = Ideal.ofList s) :
    (∑ b : Fin (t.length + 1), (-1 : ℤ) ^ (b : ℕ) *
      Koszul.seqEuler (fun j => φ (s.get j))
        (correspondenceRemainingFirstKoszulModule f g h i z w v x.1 t ht hY b)) =
    ∑ b : Fin (s.length + 1), (-1 : ℤ) ^ (b : ℕ) *
      Koszul.seqEuler (fun j => κ (t.get j))
        (correspondenceRightRemainingFirstKoszulModule f g h i z w v x.1 s hs hZ b) :=
  sum_signed_correspondenceTripleIncidence_columnEuler_eq
    k f g h i z w v x t s ht hs hY hZ

end Stacks.Chow
