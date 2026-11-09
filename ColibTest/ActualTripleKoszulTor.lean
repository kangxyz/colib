/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.TripleRegularImmersion
import Colib.AlgebraicGeometry.Correspondences.Composition.TripleKoszulTor

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  [Flat f] [Smooth g] [IsSeparated g] [Smooth h] [IsSeparated h] [Flat i]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (t : correspondenceTripleIncidence f g h i z w v)

example : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularImmersion
    (correspondenceFourfoldDiagonalInclusion f g h i) :=
  isRegularImmersion_correspondenceFourfoldDiagonal f g h i

example : correspondenceFirstDiagonalInclusion f g h i ≫
    correspondenceSixfoldSecondMiddlePair f g h i =
      correspondenceFirstDiagonalSecondMiddlePair f g h i :=
  correspondenceFirstDiagonal_secondMiddlePair f g h i

example (a : correspondenceTripleIncidenceAmbientStalk f g h i z w v t) :
    (correspondenceTripleIncidenceDiagonalStalkQuotientIso f g h i z w v t).hom
      (Ideal.Quotient.mk _ a) =
        ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap
          (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v t)).hom a :=
  correspondenceTripleIncidenceDiagonalStalkQuotientIso_mk f g h i z w v t a

example {r : ℕ}
    (a : Fin r → correspondenceTripleIncidenceAmbientStalk f g h i z w v t)
    (ha : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v t) (List.ofFn a))
    (hker : RingHom.ker ((correspondenceFourfoldDiagonalInclusion f g h i).stalkMap
      (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v t)).hom =
        Ideal.span (Set.range a)) (n : ℕ) :
    Nonempty (correspondenceTripleIncidenceTor f g h i z w v t n ≅
      (Koszul.seqComplexTensor a
        (correspondenceTripleIncidenceSupportStalkModule f g h i z w v t)).homology n) :=
  ⟨correspondenceTripleIncidenceTorIsoKoszul f g h i z w v t a ha hker n⟩
