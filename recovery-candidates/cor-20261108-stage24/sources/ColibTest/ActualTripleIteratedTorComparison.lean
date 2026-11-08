import Colib.AlgebraicGeometry.Correspondences.Composition.TripleIteratedTorComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example [IsSeparated g] [IsSeparated h]
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) (a b : ℕ) :
    Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1)
      (correspondenceTripleIncidenceLeftIteratedTor f g h i z w v x.1 a b) ≠ ⊤ :=
  length_correspondenceTripleIncidenceLeftIteratedTor_ne_top f g h i z w v x a b

example [IsSeparated g] [IsSeparated h]
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) (a b : ℕ) :
    Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1)
      (correspondenceTripleIncidenceRightIteratedTor f g h i z w v x.1 a b) ≠ ⊤ :=
  length_correspondenceTripleIncidenceRightIteratedTor_ne_top f g h i z w v x a b

section Field

variable (k : Type u) [Field k] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (h : Z ⟶ Spec (.of k)) (i : W ⟶ Spec (.of k))
  [Smooth f] [Smooth g] [Smooth h] [Smooth i]
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example (x : correspondenceTripleIncidence f g h i z w v) (a b : ℕ)
    (hab : correspondenceTripleIncidenceTorDegreeBound k f g h i z w v x < a ∨
      correspondenceTripleIncidenceTorDegreeBound k f g h i z w v x < b) :
    IsZero (correspondenceTripleIncidenceLeftIteratedTor f g h i z w v x a b) :=
  isZero_correspondenceTripleIncidenceLeftIteratedTor_of_lt k f g h i z w v x a b hab

example (x : correspondenceTripleIncidence f g h i z w v) (a b : ℕ)
    (hab : correspondenceTripleIncidenceTorDegreeBound k f g h i z w v x < a ∨
      correspondenceTripleIncidenceTorDegreeBound k f g h i z w v x < b) :
    IsZero (correspondenceTripleIncidenceRightIteratedTor f g h i z w v x a b) :=
  isZero_correspondenceTripleIncidenceRightIteratedTor_of_lt k f g h i z w v x a b hab

example [IsSeparated g] [IsSeparated h]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    (∑ᶠ ab : ℕ × ℕ, (-1 : ℤ) ^ (ab.1 + ab.2) *
      ((Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1)
        (correspondenceTripleIncidenceLeftIteratedTor f g h i z w v x.1
          ab.1 ab.2)).toNat : ℤ)) =
    ∑ᶠ ab : ℕ × ℕ, (-1 : ℤ) ^ (ab.1 + ab.2) *
      ((Module.length (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1)
        (correspondenceTripleIncidenceRightIteratedTor f g h i z w v x.1
          ab.1 ab.2)).toNat : ℤ) :=
  finsum_signed_length_correspondenceTripleIncidence_iteratedTor_eq k f g h i z w v x

end Field

end Stacks.Chow
