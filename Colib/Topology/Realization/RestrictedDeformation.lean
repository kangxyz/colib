/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.DeformationRetract.Basic
public import Colib.Topology.Realization.MonoPullbackRange
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Restricting a deformation to a simplicial inverse image

The zero endpoint of a factored deformation lands in the realized
Cartesian intersection. The inherited homotopy fixes the whole inverse
image, as in Jardine, *Simplicial presheaves*, Lemma 2.4, pp. 65–66.
https://doi.org/10.1016/0022-4049(87)90100-9
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory Topology
open scoped Simplicial Topology unitInterval

universe u

namespace SSet

/-- A deformation on a subspace, when its whole homotopy factors through
a larger simplicial subspace, gives a relative homotopy to the original
inverse image in that larger subspace. -/
theorem exists_relativeHomotopy_of_factored_deformation
    {A P X Y Z : SSet.{u}} {a : P ⟶ Y} {b : P ⟶ X} {f : Y ⟶ Z} {g : X ⟶ Z}
    [Mono f] [Mono g] (sq : IsPullback a b f g)
    (R : TopCat.CylinderStrongDeformationRetract (SSet.toTop.map g))
    (i : A ⟶ Y) (H : SSet.toTop.obj A ⊗ TopCat.I ⟶ SSet.toTop.obj Y)
    (hH : H ≫ SSet.toTop.map f = (SSet.toTop.map (i ≫ f) ▷ TopCat.I) ≫ R.H) :
    ∃ (r : C(|A|, |P|))
      (K : ((SSet.toTop.map a).hom.comp r).Homotopy (SSet.toTop.map i).hom),
      ∀ (t : unitInterval) (x : |A|), (SSet.toTop.map i) x ∈ Set.range (SSet.toTop.map a) →
        K (t, x) = (SSet.toTop.map i) x := by
  let F := SSet.toTop.map f
  let G := SSet.toTop.map g
  let inc := SSet.toTop.map i
  let A' := SSet.toTop.map a
  let : Mono a := PullbackCone.mono_fst_of_is_pullback_of_mono sq.isLimit
  have hF : Function.Injective F := (realization_mono_isClosedEmbedding f).injective
  have hA : IsEmbedding A' := (realization_mono_isClosedEmbedding a).isEmbedding
  have hw : A' ≫ F = SSet.toTop.map b ≫ G := by
    dsimp only [A', F, G]
    rw [← Functor.map_comp, ← Functor.map_comp, sq.w]
  have hH' : H ≫ F = ((inc ≫ F) ▷ TopCat.I) ≫ R.H := by
    simpa only [Functor.map_comp] using hH
  have heval (t : TopCat.I) (x : |A|) : F (H (x, t)) = R.H (F (inc x), t) :=
    ConcreteCategory.congr_hom hH' (x, t)
  let H₀ : SSet.toTop.obj A ⟶ SSet.toTop.obj Y := TopCat.ι₀ ≫ H
  have he₀ : H₀ ≫ F = inc ≫ F ≫ R.r ≫ G := by
    dsimp only [H₀]
    rw [Category.assoc, hH', ← Category.assoc, TopCat.ι₀_comp,
      Category.assoc, R.H₀, Category.assoc]
  have h₀ (x : |A|) : H₀ x ∈ Set.range A' := by
    have hx : F (H₀ x) ∈ Set.range (SSet.toTop.map (a ≫ f)) := by
      rw [realization_range_intersection_of_isPullback sq]
      exact ⟨⟨H₀ x, rfl⟩, R.r (F (inc x)), (ConcreteCategory.congr_hom he₀ x).symm⟩
    obtain ⟨p, hp⟩ := hx
    refine ⟨p, hF ?_⟩
    change (SSet.toTop.map a ≫ SSet.toTop.map f) p = F (H₀ x)
    rwa [← Functor.map_comp]
  let r₀ : C(|A|, Set.range A') := ⟨fun x => ⟨H₀ x, h₀ x⟩, H₀.hom.continuous.subtype_mk _⟩
  let r : C(|A|, |P|) := (hA.toHomeomorph.symm : C(Set.range A', |P|)).comp r₀
  have hr : H₀ = TopCat.ofHom (A'.hom.comp r) := by
    apply ConcreteCategory.hom_ext
    intro x
    change (r₀ x).val = (hA.toHomeomorph (hA.toHomeomorph.symm (r₀ x))).val
    exact (congrArg Subtype.val (hA.toHomeomorph.apply_symm_apply (r₀ x))).symm
  have he₁ : TopCat.ι₁ ≫ H = inc := by
    ext x
    apply hF
    have he : (TopCat.ι₁ ≫ H) ≫ F = inc ≫ F := by
      rw [Category.assoc, hH', ← Category.assoc, TopCat.ι₁_comp,
        Category.assoc, R.H₁, Category.comp_id]
    exact ConcreteCategory.congr_hom he x
  refine ⟨r, TopCat.homotopyOfCylinder H hr he₁, ?_⟩
  rintro t x ⟨p, hp⟩
  apply hF
  change F (H (x, ULift.up t)) = F (inc x)
  rw [heval, ← hp]
  have e : F (A' p) = G (SSet.toTop.map b p) := ConcreteCategory.congr_hom hw p
  rw [e]
  exact ConcreteCategory.congr_hom R.fixed (SSet.toTop.map b p, ULift.up t)

end SSet
