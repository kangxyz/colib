module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteEuler

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i) [IsSeparated h]
  [IsLocallyNoetherian (correspondenceLeftIntermediateImageProduct f g h i z w v)]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (x : genericPoints (correspondenceLeftImageIncidence f g h i z w v))

local notation3 (prettyPrint := false) "R" => correspondenceRemainingImageStalk f g h i z w v x.1
local notation3 (prettyPrint := false) "B" => correspondenceRemainingFiniteRing f g h i z w v x.1
local notation3 (prettyPrint := false) "A" => (pullback h h).presheaf.stalk
  (correspondenceLeftImageMiddlePair f g h i z w v
    (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1))
local notation3 (prettyPrint := false) "α" => correspondenceRemainingImageMiddleStalkMap f g h i z w v x.1


example {r : ℕ} (s : Fin r → A)
    (hr : RingTheory.Sequence.IsRegular A (List.ofFn s))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x.1)) =
          Ideal.span (Set.range s))
    (M : ModuleCat.{u} B) [Module.Finite B M] (n : ℕ) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x.1
    Module.length B
      ((Koszul.seqComplexTensor (fun j => algebraMap R B (α (s j))) M).homology n) ≠ ⊤ :=
  length_correspondenceRemainingFiniteKoszul_ne_top f g h i z w v hz hw x s hr hs M n

#check length_correspondenceRemainingFiniteKoszul_ne_top
#check sum_signed_seqEuler_correspondenceRemainingFiniteModel

end Stacks.Chow
