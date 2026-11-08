module

import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFirstHomologyEuler

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- Actual homology modules in all degrees; no substituted coefficient equality is assumed.
example
    [IsSeparated g] [IsSeparated h]
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v))
    (t s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1))
    (hr : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1) t)
    (ht : IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1) = Ideal.ofList t)
    (hs : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1) = Ideal.ofList s)
    (J : Finset ℕ) :
    let R := correspondenceRemainingOriginalStalk f g h i z w v x.1
    let b := s.map (correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x.1)
    let H := fun n => correspondenceRemainingFirstKoszulModule f g h i z w v x.1 t hr ht n
    ∑ n ∈ J, (-1 : ℤ) ^ n * Koszul.seqEuler b.get (H n) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        (∑ n ∈ J, (-1 : ℤ) ^ n *
          ((Module.length (Localization.AtPrime p.1.asIdeal)
            (LocalizedModule p.1.asIdeal.primeCompl (H n))).toNat : ℤ)) *
              Koszul.seqEuler b.get (R ⧸ p.1.asIdeal) :=
  sum_signed_correspondenceRemainingFirstHomologyEuler_eq_finsum f g h i z w v x t s hr ht hs J
