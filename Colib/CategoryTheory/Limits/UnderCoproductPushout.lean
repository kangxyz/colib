/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# The underlying pushout of a coproduct in an under category

The coproduct of objects under `P` identifies all their specified maps
from `P` by a single pushout. Both the coprojections and the coproduct map
are the original maps of the chosen coproducts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.Under

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C]
  {P : C} {ι : Type w} (X : ι → Under P) [HasCoproduct X]

/-- The sum of the specified maps from the common source. -/
abbrev coproductSourceMap : (∐ fun _ : ι => P) ⟶ ∐ fun i => (X i).right :=
  Limits.Sigma.map (fun i => (X i).hom)

/-- The original coprojections after forgetting the maps from the common source. -/
abbrev coproductRightMap : (∐ fun i => (X i).right) ⟶ (∐ X).right :=
  Limits.Sigma.desc (fun i => (Limits.Sigma.ι X i).right)

/-- The underlying coproduct is the pushout along the fold on the common source. -/
theorem coproductRight_isPushout :
    IsPushout (coproductSourceMap X) (Limits.Sigma.desc (fun _ : ι => 𝟙 P))
      (coproductRightMap X) (∐ X).hom := by
  let a := coproductSourceMap X
  let b : (∐ fun _ : ι => P) ⟶ P := Limits.Sigma.desc (fun _ : ι => 𝟙 P)
  let d := coproductRightMap X
  have h : a ≫ d = b ≫ (∐ X).hom := by
    apply Limits.Sigma.hom_ext
    intro i
    rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, Limits.Sigma.ι_comp_desc,
      ← Category.assoc, Limits.Sigma.ι_comp_desc, Category.id_comp]
    exact Under.w (Limits.Sigma.ι X i)
  let lift (s : PushoutCocone a b) (i : ι) : X i ⟶ Under.mk s.inr :=
    Under.homMk (Limits.Sigma.ι (fun i => (X i).right) i ≫ s.inl) (by
      have hw := congrArg (Limits.Sigma.ι (fun _ : ι => P) i ≫ ·) s.condition
      rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc,
        ← Category.assoc (Limits.Sigma.ι (fun _ : ι => P) i),
        Limits.Sigma.ι_comp_desc, Category.id_comp] at hw
      exact hw)
  let l (s : PushoutCocone a b) : (∐ X) ⟶ Under.mk s.inr := Limits.Sigma.desc (lift s)
  refine IsPushout.of_isColimit' ⟨h⟩ (PushoutCocone.IsColimit.mk h (fun s => (l s).right)
    ?_ ?_ ?_)
  · intro s
    apply Limits.Sigma.hom_ext
    intro i
    rw [← Category.assoc, Limits.Sigma.ι_comp_desc]
    exact congrArg Under.Hom.right (Limits.Sigma.ι_comp_desc (lift s) i)
  · intro s
    exact Under.w (l s)
  · intro s m hm hn
    let m' : (∐ X) ⟶ Under.mk s.inr := Under.homMk m hn
    have he : m' = l s := by
      apply Limits.Sigma.hom_ext
      intro i
      apply Under.UnderMorphism.ext
      change (Limits.Sigma.ι X i).right ≫ m = (Limits.Sigma.ι X i).right ≫ (l s).right
      have hl := congrArg (Limits.Sigma.ι (fun i => (X i).right) i ≫ ·) hm
      rw [← Category.assoc, Limits.Sigma.ι_comp_desc] at hl
      exact hl.trans (congrArg Under.Hom.right (Limits.Sigma.ι_comp_desc (lift s) i)).symm
    exact congrArg Under.Hom.right he

variable {X} {Y : ι → Under P} [HasCoproduct Y]

/-- The underlying coproduct map agrees with the sum of the original maps on all summands. -/
theorem coproductRightMap_sigmaMap (f : ∀ i, X i ⟶ Y i) :
    coproductRightMap X ≫ (Limits.Sigma.map f).right =
      Limits.Sigma.map (fun i => (f i).right) ≫ coproductRightMap Y := by
  apply Limits.Sigma.hom_ext
  intro i
  rw [← Category.assoc, Limits.Sigma.ι_comp_desc, ← Category.assoc, Limits.Sigma.ι_map,
    Category.assoc, Limits.Sigma.ι_comp_desc]
  exact congrArg Under.Hom.right (Limits.Sigma.ι_map f i)

/-- The underlying coproduct map is a cobase change of the sum of the underlying maps. -/
theorem sigmaMap_right_isPushout [HasPushouts C] (f : ∀ i, X i ⟶ Y i) :
    IsPushout (Limits.Sigma.map (fun i => (f i).right)) (coproductRightMap X)
      (coproductRightMap Y) (Limits.Sigma.map f).right := by
  have ha : coproductSourceMap X ≫ Limits.Sigma.map (fun i => (f i).right) =
      coproductSourceMap Y := by
    rw [Limits.Sigma.map_comp_map]
    exact congrArg Limits.Sigma.map (funext (fun i => Under.w (f i)))
  have h : (∐ X).hom ≫ (Limits.Sigma.map f).right = (∐ Y).hom := Under.w (Limits.Sigma.map f)
  apply IsPushout.of_left _ (coproductRightMap_sigmaMap f).symm (coproductRight_isPushout X)
  rw [ha, h]
  exact coproductRight_isPushout Y

end CategoryTheory.Under
