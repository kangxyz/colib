/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Complement comparison for common full closed fibers

Adapted from `Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Cartier/PunctureComparison.lean`
at motivic commit a6805c4a87cdfd7717dd7a94039246a167f15380,
blob dd15cd6c36b803181eff6b1b9d406891fbea1197.
This generic geometric lemma compares actual open complements. It does not
assert a cylinder chart producer or a cohomological restriction theorem.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

theorem range_fst_of_cartesian {D A B C : Scheme.{u}}
    {d : D ⟶ A} {e : D ⟶ B} {a : A ⟶ C} {i : B ⟶ C}
    (h : IsPullback d e a i) : Set.range d = a ⁻¹' Set.range i := by
  rw [← h.isoPullback_hom_fst]
  change Set.range ((pullback.fst a i) ∘ h.isoPullback.hom) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr h.isoPullback.hom.surjective,
    Set.image_univ, Scheme.Pullback.range_fst]

/-- Two full closed-fiber squares identify the pullback of an actual open
complement with the other actual open complement, over the same base. -/
theorem exists_open_complement_comparison {S : Scheme.{u}}
    {U Y V D T Q : SmoothSite S} (j : U ⟶ Y) [IsOpenImmersion j.left]
    (a : V ⟶ Y) (b : V ⟶ T) (d : D ⟶ V)
    {Z : Scheme.{u}} (i : Z ⟶ Y.left) (e : D.left ⟶ Z)
    (z : D ⟶ T) (c : Q ⟶ T) [IsOpenImmersion c.left]
    (hpa : IsPullback d.left e a.left i)
    (hpb : IsPullback d.left (𝟙 _) b.left z.left)
    (hcomp : Set.range i = (Set.range j.left)ᶜ)
    (hzcomp : Set.range z.left = (Set.range c.left)ᶜ) :
    IsPullback (etalePullbackFst j a) (etalePullbackSnd j a) j a ∧
      ∃ t : etalePullback j a ⟶ Q,
        IsPullback t (etalePullbackSnd j a) c b := by
  let W := etalePullback j a
  let w := etalePullbackSnd j a
  have : IsOpenImmersion w.left :=
    inferInstanceAs (IsOpenImmersion (pullback.snd j.left a.left))
  refine ⟨IsPullback.of_isLimit (etalePullbackConeIsLimit j a), ?_⟩
  have hr : Set.range w.left = b.left ⁻¹' Set.range c.left := by
    have hj : Set.range j.left = (Set.range i)ᶜ := by rw [hcomp, compl_compl]
    calc
      Set.range w.left = a.left ⁻¹' Set.range j.left :=
        Scheme.Pullback.range_snd j.left a.left
      _ = (Set.range d.left)ᶜ := by
        rw [hj, Set.preimage_compl, ← range_fst_of_cartesian hpa]
      _ = b.left ⁻¹' Set.range c.left := by
        rw [range_fst_of_cartesian hpb, hzcomp,
          Set.preimage_compl, compl_compl]
  have hlift : Set.range (w.left ≫ b.left) ⊆ Set.range c.left := by
    rintro _ ⟨x, rfl⟩
    exact (show w.left x ∈ b.left ⁻¹' Set.range c.left from hr ▸ ⟨x, rfl⟩)
  let t₀ := IsOpenImmersion.lift c.left (w.left ≫ b.left) hlift
  have ht₀ : t₀ ≫ c.left = w.left ≫ b.left := IsOpenImmersion.lift_fac _ _ _
  let t : W ⟶ Q := homMk t₀ (by
    rw [← MorphismProperty.Over.w c, ← Category.assoc, ht₀,
      Category.assoc, MorphismProperty.Over.w b, MorphismProperty.Over.w w])
  refine ⟨t, ?_⟩
  apply IsPullback.of_map_of_faithful (forgetScheme S)
  apply IsOpenImmersion.isPullback t₀ w.left c.left b.left ht₀.symm
  ext x
  change b.left x ∈ Set.range c.left ↔ x ∈ Set.range w.left
  exact (Set.ext_iff.mp hr x).symm

end AlgebraicGeometry.Scheme.SmoothSite
