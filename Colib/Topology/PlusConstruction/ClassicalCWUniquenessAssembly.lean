/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.DoubleMappingCylinder.ComparisonDescent

/-!
# Ordinary uniqueness from the original double cylinder legs

The mixed-cylinder legs give a comparison under the source. The left leg of
the self cylinder gives homotopy cancellation into any same-universe space.
Using cancellation for the original under-source homotopies then gives
ordinary uniqueness; it asserts no coherence between those homotopies.

This is the assembly in
`Quillen/Topology/PlusConstruction/ClassicalCWUniqueness.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, with the actual endpoint
equivalences as hypotheses.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval

universe u

namespace TopCat.DoubleCylinder

variable {A B C D S : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
variable {ls : A ⊗ TopCat.I ⟶ S} {es : TopCat.of (B ⊕ B) ⟶ S}
variable {lm : A ⊗ TopCat.I ⟶ D} {em : TopCat.of (B ⊕ C) ⟶ D}

/-- Maps with homotopic restrictions to the original source are homotopic
by cancellation through the actual self cylinder. -/
theorem homotopic_underSource_of_leftLegEquiv
    (ss : IsPushout (TopCat.intervalEndpoints A) (endMap f f) ls es)
    (L : ContinuousMap.HomotopyEquiv B S) (hL : L.toFun = gapLeftEndpoint es)
    {Y : Type u} [TopologicalSpace Y] (k : C(A, Y)) (h₀ h₁ : C(B, Y))
    (H₀ : (h₀.comp f.hom).Homotopic k) (H₁ : (h₁.comp f.hom).Homotopic k) :
    h₀.Homotopic h₁ :=
  ⟨homotopyCancelOfLeftLegEquiv f ss L hL h₀ h₁ (H₀.some.trans H₁.some.symm)⟩

/-- The two mixed-cylinder legs give a comparison equivalence under the original
source, and the left self-cylinder leg gives ordinary uniqueness of that comparison. -/
theorem exists_homotopyEquiv_underSource_of_legEquivs
    (sm : IsPushout (TopCat.intervalEndpoints A) (endMap f g) lm em)
    (ss : IsPushout (TopCat.intervalEndpoints A) (endMap f f) ls es)
    (I : ContinuousMap.HomotopyEquiv B D) (J : ContinuousMap.HomotopyEquiv C D)
    (L : ContinuousMap.HomotopyEquiv B S)
    (hI : I.toFun = gapLeftEndpoint em) (hJ : J.toFun = gapRightEndpoint em)
    (hL : L.toFun = gapLeftEndpoint es) :
    ∃ h : ContinuousMap.HomotopyEquiv B C,
      (h.toFun.comp f.hom).Homotopic g.hom ∧
        ∀ k : C(B, C), (k.comp f.hom).Homotopic g.hom → k.Homotopic h.toFun := by
  let h := I.trans J.symm
  have H : (h.toFun.comp f.hom).Homotopic g.hom :=
    ⟨comparisonUnderSourceOfLegEquivs f g sm I J hI hJ⟩
  exact ⟨h, H, fun k Hk ↦
    homotopic_underSource_of_leftLegEquiv f ss L hL g.hom k h.toFun Hk H⟩

end TopCat.DoubleCylinder
