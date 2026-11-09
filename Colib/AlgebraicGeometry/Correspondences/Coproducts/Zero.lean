/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Category
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# The actual empty scheme as the zero correspondence object

The native correspondence cycle is a function on the actual scheme product.
If either endpoint is empty, every point of that product is impossible. Thus
all signed cycles vanish, without changing their representation or imposing
integrality or connectedness on any other object.

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Coproducts/Binary.lean`,
blob `993ffbf915b22adc8cec07f62ccbc3e35049608e`, empty-object section.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]

/-- Every actual correspondence with empty source is the zero native cycle. -/
theorem hom_eq_zero_of_isEmpty_source {X Y : Cor k} [IsEmpty X.toSmoothSite.left]
    (α : X ⟶ Y) : α = 0 := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro z
  exact isEmptyElim (show X.toSmoothSite.left from
    pullback.fst X.toSmoothSite.hom Y.toSmoothSite.hom z)

instance hom_subsingleton_of_isEmpty_source {X Y : Cor k} [IsEmpty X.toSmoothSite.left] :
    Subsingleton (X ⟶ Y) :=
  ⟨fun α β => (hom_eq_zero_of_isEmpty_source k α).trans
    (hom_eq_zero_of_isEmpty_source k β).symm⟩

/-- Every actual correspondence with empty target is the zero native cycle. -/
theorem hom_eq_zero_of_isEmpty_target {X Y : Cor k} [IsEmpty Y.toSmoothSite.left]
    (α : X ⟶ Y) : α = 0 := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro z
  exact isEmptyElim (show Y.toSmoothSite.left from
    pullback.snd X.toSmoothSite.hom Y.toSmoothSite.hom z)

instance hom_subsingleton_of_isEmpty_target {X Y : Cor k} [IsEmpty Y.toSmoothSite.left] :
    Subsingleton (X ⟶ Y) :=
  ⟨fun α β => (hom_eq_zero_of_isEmpty_target k α).trans
    (hom_eq_zero_of_isEmpty_target k β).symm⟩

/-- The actual empty scheme, with its unique structural morphism to the base field. -/
def empty : Cor k := ⟨Scheme.SmoothSite.mk (Scheme.emptyTo (Spec (.of k)))⟩

instance empty_isEmpty : IsEmpty (empty k).toSmoothSite.left :=
  inferInstanceAs (IsEmpty (∅ : Scheme.{u}))

/-- The actual empty scheme is a zero object in the genuine correspondence category. -/
theorem empty_isZero : IsZero (empty k) where
  unique_to _ := ⟨{ default := 0, uniq := hom_eq_zero_of_isEmpty_source k }⟩
  unique_from _ := ⟨{ default := 0, uniq := hom_eq_zero_of_isEmpty_target k }⟩

instance : HasZeroObject (Cor k) := ⟨⟨empty k, empty_isZero k⟩⟩

end AlgebraicGeometry.Cor
