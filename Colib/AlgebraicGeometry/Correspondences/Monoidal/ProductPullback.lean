/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The product of two incidence pullbacks

The product over the base of two pullbacks is the pullback of the two product
maps. The isomorphism preserves all four original coordinates. Applied to
finite correspondence supports, it retains the entire two incidence schemes,
including their nilpotents, before any Tor or cycle comparison.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {A B D E M N S : C}
  (f : A ⟶ M) (g : B ⟶ M) (h : D ⟶ N) (i : E ⟶ N)
  (p : M ⟶ S) (q : N ⟶ S)

/-- The product map of the first legs of the two cospans. -/
def pullbackProductFirstMap : pullback (f ≫ p) (h ≫ q) ⟶ pullback p q :=
  pullback.lift (pullback.fst (f ≫ p) (h ≫ q) ≫ f)
    (pullback.snd (f ≫ p) (h ≫ q) ≫ h) (by
    simpa only [Category.assoc] using
      (pullback.condition (f := f ≫ p) (g := h ≫ q)))

/-- The product map of the second legs of the two cospans. -/
def pullbackProductSecondMap : pullback (g ≫ p) (i ≫ q) ⟶ pullback p q :=
  pullback.lift (pullback.fst (g ≫ p) (i ≫ q) ≫ g)
    (pullback.snd (g ≫ p) (i ≫ q) ≫ i) (by
    simpa only [Category.assoc] using
      (pullback.condition (f := g ≫ p) (g := i ≫ q)))

local notation "a" => pullback.fst f g ≫ f ≫ p
local notation "b" => pullback.fst h i ≫ h ≫ q
local notation "l" => pullbackProductFirstMap f h p q
local notation "r" => pullbackProductSecondMap g i p q

/-- Exchange the middle two coordinates of the product of the incidence pullbacks. -/
def pullbackProductInterchangeHom : pullback a b ⟶ pullback l r :=
  pullback.lift
    (pullback.lift (pullback.fst a b ≫ pullback.fst f g)
      (pullback.snd a b ≫ pullback.fst h i) (by
        simpa only [Category.assoc] using (pullback.condition (f := a) (g := b))))
    (pullback.lift (pullback.fst a b ≫ pullback.snd f g)
      (pullback.snd a b ≫ pullback.snd h i) (by
        simpa only [Category.assoc, pullback.condition_assoc (f := f) (g := g),
          pullback.condition_assoc (f := h) (g := i)] using
          (pullback.condition (f := a) (g := b))))
    (by
      apply pullback.hom_ext <;>
        simp [pullbackProductFirstMap, pullbackProductSecondMap, Category.assoc,
          pullback.condition])

/-- Recover the two original incidence coordinates from the product pullback. -/
def pullbackProductInterchangeInv : pullback l r ⟶ pullback a b :=
  pullback.lift
    (pullback.lift (pullback.fst l r ≫ pullback.fst (f ≫ p) (h ≫ q))
      (pullback.snd l r ≫ pullback.fst (g ≫ p) (i ≫ q)) (by
        have he := congrArg (fun t => t ≫ pullback.fst p q)
          (pullback.condition (f := l) (g := r))
        simpa only [Category.assoc, pullbackProductFirstMap, pullbackProductSecondMap,
          pullback.lift_fst] using he))
    (pullback.lift (pullback.fst l r ≫ pullback.snd (f ≫ p) (h ≫ q))
      (pullback.snd l r ≫ pullback.snd (g ≫ p) (i ≫ q)) (by
        have he := congrArg (fun t => t ≫ pullback.snd p q)
          (pullback.condition (f := l) (g := r))
        simpa only [Category.assoc, pullbackProductFirstMap, pullbackProductSecondMap,
          pullback.lift_snd] using he))
    (by
      simpa only [Category.assoc, pullback.lift_fst_assoc] using
        congrArg (fun t => pullback.fst l r ≫ t)
          (pullback.condition (f := f ≫ p) (g := h ≫ q)))

/-- The full product of two incidence schemes is the incidence of the two product supports. -/
def pullbackProductInterchangeIso : pullback a b ≅ pullback l r where
  hom := pullbackProductInterchangeHom f g h i p q
  inv := pullbackProductInterchangeInv f g h i p q
  hom_inv_id := by
    apply pullback.hom_ext <;> apply pullback.hom_ext <;>
      simp [pullbackProductInterchangeHom, pullbackProductInterchangeInv, Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext <;> apply pullback.hom_ext <;>
      simp [pullbackProductInterchangeHom, pullbackProductInterchangeInv, Category.assoc]

@[reassoc (attr := simp)]
theorem pullbackProductInterchangeIso_hom_fst_fst :
    (pullbackProductInterchangeIso f g h i p q).hom ≫ pullback.fst l r ≫
      pullback.fst (f ≫ p) (h ≫ q) = pullback.fst a b ≫ pullback.fst f g := by
  simp [pullbackProductInterchangeIso, pullbackProductInterchangeHom]

@[reassoc (attr := simp)]
theorem pullbackProductInterchangeIso_hom_fst_snd :
    (pullbackProductInterchangeIso f g h i p q).hom ≫ pullback.fst l r ≫
      pullback.snd (f ≫ p) (h ≫ q) = pullback.snd a b ≫ pullback.fst h i := by
  simp [pullbackProductInterchangeIso, pullbackProductInterchangeHom]

@[reassoc (attr := simp)]
theorem pullbackProductInterchangeIso_hom_snd_fst :
    (pullbackProductInterchangeIso f g h i p q).hom ≫ pullback.snd l r ≫
      pullback.fst (g ≫ p) (i ≫ q) = pullback.fst a b ≫ pullback.snd f g := by
  simp [pullbackProductInterchangeIso, pullbackProductInterchangeHom]

@[reassoc (attr := simp)]
theorem pullbackProductInterchangeIso_hom_snd_snd :
    (pullbackProductInterchangeIso f g h i p q).hom ≫ pullback.snd l r ≫
      pullback.snd (g ≫ p) (i ≫ q) = pullback.snd a b ≫ pullback.snd h i := by
  simp [pullbackProductInterchangeIso, pullbackProductInterchangeHom]

end CategoryTheory.Limits

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {A B D E S : C} (f : A ⟶ S) (g : B ⟶ S) (h : D ⟶ S) (i : E ⟶ S)

local notation "a" => pullback.fst f g ≫ f
local notation "b" => pullback.fst h i ≫ h

/-- Exchange the two middle factors of four literal products over the same base. -/
def pullbackFourShuffleHom : pullback a b ⟶
    pullback (pullback.fst f h ≫ f) (pullback.fst g i ≫ g) :=
  pullback.lift
    (pullback.lift (pullback.fst a b ≫ pullback.fst f g)
      (pullback.snd a b ≫ pullback.fst h i) (by
        simpa only [Category.assoc] using (pullback.condition (f := a) (g := b))))
    (pullback.lift (pullback.fst a b ≫ pullback.snd f g)
      (pullback.snd a b ≫ pullback.snd h i) (by
        simpa only [Category.assoc, pullback.condition (f := f) (g := g),
          pullback.condition (f := h) (g := i)] using
          (pullback.condition (f := a) (g := b))))
    (by
      simpa only [Category.assoc, pullback.lift_fst_assoc] using
        congrArg (fun t => pullback.fst a b ≫ t) (pullback.condition (f := f) (g := g)))

/-- The middle-factor exchange is its own inverse, with the arguments exchanged. -/
def pullbackFourShuffleIso : pullback a b ≅
    pullback (pullback.fst f h ≫ f) (pullback.fst g i ≫ g) where
  hom := pullbackFourShuffleHom f g h i
  inv := pullbackFourShuffleHom f h g i
  hom_inv_id := by
    apply pullback.hom_ext <;> apply pullback.hom_ext <;>
      simp [pullbackFourShuffleHom, Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext <;> apply pullback.hom_ext <;>
      simp [pullbackFourShuffleHom, Category.assoc]

@[reassoc (attr := simp)]
theorem pullbackFourShuffleIso_hom_fst_fst :
    (pullbackFourShuffleIso f g h i).hom ≫
      pullback.fst (pullback.fst f h ≫ f) (pullback.fst g i ≫ g) ≫ pullback.fst f h =
        pullback.fst a b ≫ pullback.fst f g := by
  simp [pullbackFourShuffleIso, pullbackFourShuffleHom]

@[reassoc (attr := simp)]
theorem pullbackFourShuffleIso_hom_fst_snd :
    (pullbackFourShuffleIso f g h i).hom ≫
      pullback.fst (pullback.fst f h ≫ f) (pullback.fst g i ≫ g) ≫ pullback.snd f h =
        pullback.snd a b ≫ pullback.fst h i := by
  simp [pullbackFourShuffleIso, pullbackFourShuffleHom]

@[reassoc (attr := simp)]
theorem pullbackFourShuffleIso_hom_snd_fst :
    (pullbackFourShuffleIso f g h i).hom ≫
      pullback.snd (pullback.fst f h ≫ f) (pullback.fst g i ≫ g) ≫ pullback.fst g i =
        pullback.fst a b ≫ pullback.snd f g := by
  simp [pullbackFourShuffleIso, pullbackFourShuffleHom]

@[reassoc (attr := simp)]
theorem pullbackFourShuffleIso_hom_snd_snd :
    (pullbackFourShuffleIso f g h i).hom ≫
      pullback.snd (pullback.fst f h ≫ f) (pullback.fst g i ≫ g) ≫ pullback.snd g i =
        pullback.snd a b ≫ pullback.snd h i := by
  simp [pullbackFourShuffleIso, pullbackFourShuffleHom]

end CategoryTheory.Limits
