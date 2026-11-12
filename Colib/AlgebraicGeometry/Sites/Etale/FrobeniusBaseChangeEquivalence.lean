/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.IteratedFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusDescent

/-!
# Small étale base change by the actual iterated relative Frobenius

Full faithfulness is native universal-homeomorphism descent. Essential surjectivity
uses the actual first projection and the native absolute-Frobenius site isomorphism.
No equivalence of smooth sites over an imperfect field is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius Stacks.EtaleCohomology

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme

/-- The original small étale pullback along a universal homeomorphism is fully faithful. -/
def smallEtaleBaseChangeFullyFaithful {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversalHomeomorphism f] : (smallEtaleBaseChange f).FullyFaithful := by
  let : (smallEtaleBaseChange f).Full :=
    Stacks.Etale.etalePullback_full_of_universalHomeomorphism f
  let : (smallEtaleBaseChange f).Faithful :=
    Stacks.Etale.etalePullback_faithful_of_universalHomeomorphism f
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- Base change along the identity has the original étale object as an essential preimage. -/
theorem smallEtaleBaseChange_id_essSurj (X : Scheme.{u}) :
    (smallEtaleBaseChange (𝟙 X)).EssSurj := by
  refine ⟨fun U ↦ ⟨U, ⟨?_⟩⟩⟩
  exact MorphismProperty.Over.isoMk
    { hom := pullback.fst U.hom (𝟙 X)
      inv := pullback.lift (𝟙 U.left) U.hom (by simp)
      hom_inv_id := by apply pullback.hom_ext <;> simp [pullback.condition]
      inv_hom_id := by simp }
    (by
      change pullback.fst U.hom (𝟙 X) ≫ U.hom = pullback.snd U.hom (𝟙 X)
      exact (pullback.condition (f := U.hom) (g := 𝟙 X)).trans (Category.comp_id _))

/-- The original absolute-Frobenius pullback is essentially surjective, including exponent zero. -/
theorem smallEtaleBaseChange_absoluteFrobeniusPow_essSurj
    (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p) (n : ℕ) :
    (smallEtaleBaseChange (absoluteFrobeniusPow X p hX n)).EssSurj := by
  by_cases hn : n = 0
  · subst n
    exact smallEtaleBaseChange_id_essSurj X
  · exact Functor.essSurj_of_iso (absoluteFrobeniusPowEtaleSiteIso X p hX hn)

namespace SmoothSite

variable {S : Scheme.{u}} (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)

/-- Affineness of the actual Frobenius twist follows from its original affine pullback. -/
instance nFoldFrobeniusTwist_isAffine [IsAffine S] (n : ℕ) (X : SmoothSite S)
    [IsAffine X.left] : IsAffine (nFoldFrobeniusTwist p hS n X).left :=
  inferInstanceAs (IsAffine
    (pullback (X := X.left) (Y := S) (Z := S) X.hom (absoluteFrobeniusPow S p hS n)))

/-- Actual small étale base change by the n-fold relative Frobenius is an equivalence.
The proof factors the absolute Frobenius through the actual twist projection. -/
theorem smallEtaleBaseChange_nFoldRelativeFrobenius_isEquivalence
    (n : ℕ) (X : SmoothSite S) :
    (smallEtaleBaseChange (nFoldRelativeFrobenius p hS n X).left).IsEquivalence := by
  let q := (nFoldRelativeFrobenius p hS n X).left
  let π := pullback.fst X.hom (absoluteFrobeniusPow S p hS n)
  let hX := isInCharacteristic_of_hom X.hom p hS
  have hqπ : q ≫ π = absoluteFrobeniusPow X.left p hX n :=
    _root_.AlgebraicGeometry.nFoldRelativeFrobenius_fst S p hS n ((forget S).obj X)
  let := (smallEtaleBaseChangeFullyFaithful q).full
  let := (smallEtaleBaseChangeFullyFaithful q).faithful
  have : (smallEtaleBaseChange (q ≫ π)).EssSurj := by
    rw [hqπ]
    exact smallEtaleBaseChange_absoluteFrobeniusPow_essSurj X.left p hX n
  have : (smallEtaleBaseChange π ⋙ smallEtaleBaseChange q).EssSurj :=
    Functor.essSurj_of_iso (smallEtaleBaseChangeComp q π)
  have : (smallEtaleBaseChange q).EssSurj := by
    refine ⟨fun U ↦ ⟨(smallEtaleBaseChange π).obj
      ((smallEtaleBaseChange π ⋙ smallEtaleBaseChange q).objPreimage U), ?_⟩⟩
    exact ⟨(smallEtaleBaseChange π ⋙ smallEtaleBaseChange q).objObjPreimageIso U⟩
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end SmoothSite
end AlgebraicGeometry.Scheme
