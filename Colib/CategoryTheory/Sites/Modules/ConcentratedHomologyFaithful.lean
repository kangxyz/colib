/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Modules.NormalizedConcentratedDerivedIso

/-!
# Homology detects maps between concentrated objects

This is faithfulness of Hn on the corresponding heart only,
not faithfulness of all homology maps on an entire derived category and not
fullness of any derived coefficient forgetful functor.
-/

@[expose] public noncomputable section
open CategoryTheory
universe w v u
namespace DerivedCategory
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Homology detects maps between native single objects in the same degree. -/
theorem single_hom_eq_of_homology (n : ℤ) {A B : C}
    (f g : (singleFunctor C n).obj A ⟶ (singleFunctor C n).obj B)
    (h : (homologyFunctor C n).map f = (homologyFunctor C n).map g) : f = g := by
  let S := singleFunctor C n
  let H := homologyFunctor C n
  let c := singleFunctorCompHomologyFunctorIso C n
  have recover (a : S.obj A ⟶ S.obj B) :
      c.inv.app A ≫ H.map a ≫ c.hom.app B = S.preimage a := by
    rw [← S.map_preimage a]
    have hc := c.hom.naturality (S.preimage a)
    change H.map (S.map (S.preimage a)) ≫ c.hom.app B =
      c.hom.app A ≫ S.preimage a at hc
    rw [hc, ← Category.assoc, c.inv_hom_id_app, Category.id_comp, S.preimage_map]
  have hp : S.preimage f = S.preimage g := by
    rw [← recover f, ← recover g, h]
  rw [← S.map_preimage f, ← S.map_preimage g, hp]

/-- Homology detects maps when both objects are concentrated in its degree. -/
theorem concentrated_hom_eq_of_homology (n : ℤ) {X Y : DerivedCategory C}
    [X.IsGE n] [X.IsLE n] [Y.IsGE n] [Y.IsLE n]
    (f g : X ⟶ Y)
    (h : (homologyFunctor C n).map f = (homologyFunctor C n).map g) : f = g := by
  let eX := normalizedConcentratedHomologyIso X n
  let eY := normalizedConcentratedHomologyIso Y n
  have hc : eX.inv ≫ f ≫ eY.hom = eX.inv ≫ g ≫ eY.hom := by
    apply single_hom_eq_of_homology n
    simp only [Functor.map_comp, h]
  apply (cancel_epi eX.inv).mp
  apply (cancel_mono eY.hom).mp
  simpa only [Category.assoc] using hc

end DerivedCategory
