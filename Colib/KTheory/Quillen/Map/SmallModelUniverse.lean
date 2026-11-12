/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.Map.UniverseComparison
public import Colib.KTheory.Quillen.SmallModel.Functoriality
public import Colib.KTheory.Quillen.Equivalence

/-!
# Canonical K-comparison between universes of the same small model

An exact category that is essentially small in both `w₁` and `w₂` has a
canonical exact comparison from its chosen `w₁` model to its chosen `w₂`
model: realize in the SAME original category, then take its other model.
Actual equivalence units prove reflection of admissible maps and naturality
with every original exact functor. The resulting K-equivalence uses the
original cross-universe Q-map and its canonical zero-isomorphism edge.

The current application compares native lower finite-module and affine-sheaf
models with the public upper model of the same actual coherent category.
No different module-carrier category or equality of group objects is assumed.
All K-degrees, including zero, retain the original smallKMap naturality square.
-/

/-! Implementation provenance: `Quillen/KTheory/Map/SmallModelUniverse.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; actual maps and universes are retained. -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe w₁ w₂ v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFiniteBiproducts C]
  [EssentiallySmall.{w₁} C] [EssentiallySmall.{w₂} C]

/-- Realize in the same original category, then take its other chosen small model. -/
def smallModelUniverseComparison (E : ExactStructure C) :
    ExactFunctor E.smallModel.{w₁} E.smallModel.{w₂} :=
  E.smallModelToOriginal.{w₁}.comp E.originalToSmallModel.{w₂}

/-- The canonical comparison retains the original categorical equivalences. -/
instance smallModelUniverseComparison_isEquivalence (E : ExactStructure C) :
    (smallModelUniverseComparison.{w₁,w₂} E).toFunctor.IsEquivalence :=
  inferInstanceAs (((equivSmallModel.{w₁} C).inverse) ⋙
    (equivSmallModel.{w₂} C).functor).IsEquivalence

/-- Actual unit naturality proves reflection of both admissibility classes. -/
instance smallModelUniverseComparison_mapQ_isEquivalence (E : ExactStructure C) :
    (smallModelUniverseComparison.{w₁,w₂} E).mapQ.IsEquivalence := by
  apply ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro X Y i hi
    change (E.ofEquivalence (equivSmallModel.{w₂} C).symm).inflation _ at hi
    change (E.ofEquivalence (equivSmallModel.{w₁} C).symm).inflation i
    rw [E.ofEquivalence_inflation_iff] at hi ⊢
    let e := equivSmallModel.{w₂} C
    let f := (equivSmallModel.{w₁} C).inverse.map i
    have hi' : E.inflation (e.inverse.map (e.functor.map f)) := hi
    have hh := E.inflation_comp _ _ (E.inflation_of_iso (e.unitIso.app _)) hi'
    have hh' := E.inflation_comp _ _ hh (E.inflation_of_iso (e.unitIso.app _).symm)
    have hn := e.unitIso.hom.naturality f
    dsimp at hn
    change E.inflation ((e.unitIso.hom.app _ ≫ e.inverse.map (e.functor.map f)) ≫
      e.unitIso.inv.app _) at hh'
    rw [← hn] at hh'
    simpa [Category.assoc, f] using hh'
  · intro X Y i hi
    change (E.ofEquivalence (equivSmallModel.{w₂} C).symm).deflation _ at hi
    change (E.ofEquivalence (equivSmallModel.{w₁} C).symm).deflation i
    rw [E.ofEquivalence_deflation_iff] at hi ⊢
    let e := equivSmallModel.{w₂} C
    let f := (equivSmallModel.{w₁} C).inverse.map i
    have hi' : E.deflation (e.inverse.map (e.functor.map f)) := hi
    have hh := E.deflation_comp _ _ (E.deflation_of_iso (e.unitIso.app _)) hi'
    have hh' := E.deflation_comp _ _ hh (E.deflation_of_iso (e.unitIso.app _).symm)
    have hn := e.unitIso.hom.naturality f
    dsimp at hn
    change E.deflation ((e.unitIso.hom.app _ ≫ e.inverse.map (e.functor.map f)) ≫
      e.unitIso.inv.app _) at hh'
    rw [← hn] at hh'
    simpa [Category.assoc, f] using hh'

/-- The original comparison of K-groups for two model universes of the same exact category. -/
def smallKUniverseEquiv (E : ExactStructure C) (n : ℕ) :
    E.SmallK.{w₁} n ≃* E.SmallK.{w₂} n :=
  (smallModelUniverseComparison.{w₁,w₂} E).universalKEquivOfMapQIsEquivalence n

/-- The forward equivalence is the actual zero-corrected Q-map of the canonical comparison. -/
theorem smallKUniverseEquiv_toMonoidHom (E : ExactStructure C) (n : ℕ) :
    ((smallKUniverseEquiv.{w₁,w₂} E n).toMonoidHom : E.SmallK.{w₁} n →* E.SmallK.{w₂} n) =
      (smallModelUniverseComparison.{w₁,w₂} E).universalKMap n := rfl

end CategoryTheory.ExactCategory.ExactStructure

namespace CategoryTheory.ExactCategory.ExactFunctor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  [EssentiallySmall.{w₁} C] [EssentiallySmall.{w₂} C]
  [EssentiallySmall.{w₁} D] [EssentiallySmall.{w₂} D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- Actual chosen-model units identify the two comparison functors in the square. -/
def smallModelUniverseComparisonNaturalityIso (F : ExactFunctor EC ED) :
    ((EC.smallModelUniverseComparison.{w₁,w₂}).comp F.smallModel.{w₂}).toFunctor ≅
      (F.smallModel.{w₁}.comp (ED.smallModelUniverseComparison.{w₁,w₂})).toFunctor := by
  let H := (equivSmallModel.{w₁} C).inverse
  let J := F.toFunctor ⋙ (equivSmallModel.{w₂} D).functor
  let α := Functor.isoWhiskerLeft H
    (Functor.isoWhiskerRight (equivSmallModel.{w₂} C).unitIso.symm J) ≪≫
      Functor.isoWhiskerLeft H (Functor.leftUnitor J)
  let H' := H ⋙ F.toFunctor
  let K := (equivSmallModel.{w₂} D).functor
  let β := Functor.isoWhiskerLeft H'
    (Functor.isoWhiskerRight (equivSmallModel.{w₁} D).unitIso.symm K) ≪≫
      Functor.isoWhiskerLeft H' (Functor.leftUnitor K)
  exact α ≪≫ β.symm

/-- Every original smallKMap commutes with the canonical change of model universe. -/
theorem smallKUniverseEquiv_naturality (F : ExactFunctor EC ED) (n : ℕ) :
    (F.smallKMap.{w₂} n).comp (EC.smallKUniverseEquiv.{w₁,w₂} n).toMonoidHom =
      (ED.smallKUniverseEquiv.{w₁,w₂} n).toMonoidHom.comp (F.smallKMap.{w₁} n) := by
  change (F.smallModel.{w₂}.KMap n).comp
      ((EC.smallModelUniverseComparison.{w₁,w₂}).universalKMap n) =
    ((ED.smallModelUniverseComparison.{w₁,w₂}).universalKMap n).comp
      (F.smallModel.{w₁}.KMap n)
  rw [← universalKMap_eq_KMap, ← universalKMap_eq_KMap,
    ← universalKMap_comp, ← universalKMap_comp]
  exact universalKMap_eq_of_natIso
    (smallModelUniverseComparisonNaturalityIso.{w₁,w₂} F) n

end CategoryTheory.ExactCategory.ExactFunctor
