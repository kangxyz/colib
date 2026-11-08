module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFirstHomologyLength

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- Every actual first degree and remaining degree; no supplied colength or finite length.
example [IsSeparated g] [IsSeparated h]
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v))
    (t : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1))
    (htreg : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1) t)
    (ht : IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1) = Ideal.ofList t)
    {r : ℕ} (s : Fin r → correspondenceRemainingFirstAmbientStalk f g h i z w v x.1)
    (hsreg : RingTheory.Sequence.IsRegular
      (correspondenceRemainingFirstAmbientStalk f g h i z w v x.1) (List.ofFn s))
    (hs : IdealSheafData.stalk (correspondenceSecondDiagonalInclusion f g h i).ker
      (correspondenceLeftIntermediateSupportInclusion f g h i z w v
        (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x.1)) =
          Ideal.span (Set.range s)) (b a : ℕ) :
    Module.length (correspondenceRemainingOriginalStalk f g h i z w v x.1)
      ((Koszul.seqComplexTensor
        (fun j => correspondenceRemainingFirstAmbientStalkMap f g h i z w v x.1 (s j))
        (correspondenceRemainingFirstKoszulModule f g h i z w v x.1 t htreg ht b)).homology a) ≠
          ⊤ :=
  length_correspondenceRemainingFirstHomology_ne_top f g h i z w v x t htreg ht s hsreg hs b a
