/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.UnionPushout
public import Colib.CategoryTheory.Sites.Simplicial.WeakDirectedUnion
public import Mathlib.CategoryTheory.LiftingProperties.Basic
import Colib.CategoryTheory.Sites.Simplicial.StalkwiseTrivialPushout
import Mathlib.Order.Zorn

/-!
# Extending along a stalkwise weak simplicial subpresheaf

Partial lifts compatible with the original map form a preorder. A
directed union extends a chain, and a bounded weak intersection permits
one further extension at a missing section. This is the lifting part of
Jardine, *Simplicial presheaves*, Lemma 2.4, pp. 65–66.
https://doi.org/10.1016/0022-4049(87)90100-9
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.SimplicialSubpresheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {Q X Y : Cᵒᵖ ⥤ SSet.{max u v}} {A : Subpresheaf Q}
  {p : X ⟶ Y} {b : Q ⟶ Y} {a : toPresheaf A ⟶ X}
  (P : Subpresheaf Q → Prop)

/-- A partial lift through an actual intermediate subpresheaf. -/
private structure PartialLift (P : Subpresheaf Q → Prop)
    (A : Subpresheaf Q) (a : toPresheaf A ⟶ X) (p : X ⟶ Y) (b : Q ⟶ Y) where
  support : Subpresheaf Q
  le_support : A ≤ support
  lift : toPresheaf support ⟶ X
  lift_left : homOfLE le_support ≫ lift = a
  lift_right : lift ≫ p = inclusion support ≫ b
  property : P support

private instance : Preorder (PartialLift P A a p b) where
  le M N := ∃ h : M.support ≤ N.support, homOfLE h ≫ N.lift = M.lift
  le_refl M := ⟨le_rfl, by
    have h : homOfLE (le_rfl : M.support ≤ M.support) = 𝟙 _ := by
      apply (cancel_mono (inclusion M.support)).1
      rw [homOfLE_inclusion, Category.id_comp]
    rw [h, Category.id_comp]⟩
  le_trans M N K := by
    rintro ⟨hMN, eMN⟩ ⟨hNK, eNK⟩
    have h : homOfLE (hMN.trans hNK) = homOfLE hMN ≫ homOfLE hNK := by
      apply (cancel_mono (inclusion K.support)).1
      simp only [Category.assoc, homOfLE_inclusion]
    exact ⟨hMN.trans hNK, by rw [h, Category.assoc, eNK, eMN]⟩

private def initialPartialLift (w : inclusion A ≫ b = a ≫ p) (hA : P A) :
    PartialLift P A a p b where
  support := A
  le_support := le_rfl
  lift := a
  lift_left := by
    have h : homOfLE (le_rfl : A ≤ A) = 𝟙 _ := by
      apply (cancel_mono (inclusion A)).1
      rw [homOfLE_inclusion, Category.id_comp]
    rw [h, Category.id_comp]
  lift_right := w.symm
  property := hA

private theorem partialLift_bddAbove
    (hP : ∀ {ι : Type (max u v)} [Preorder ι] [IsFiltered ι]
      (B : ι → Subpresheaf Q), Monotone B → (∀ j, A ≤ B j) → (∀ j, P (B j)) → P (⨆ j, B j))
    (c : Set (PartialLift P A a p b)) (hc : IsChain (· ≤ ·) c) (hn : c.Nonempty) : BddAbove c := by
  classical
  let ι := {M : PartialLift P A a p b // M ∈ c}
  let j₀ : ι := ⟨hn.choose, hn.choose_spec⟩
  let : Nonempty ι := ⟨j₀⟩
  let : IsDirectedOrder ι := ⟨fun M N => by
    by_cases e : M.val = N.val
    · have he : M = N := Subtype.ext e
      exact ⟨N, he ▸ le_rfl, le_rfl⟩
    · rcases hc M.property N.property e with h | h
      · exact ⟨N, h, le_rfl⟩
      · exact ⟨M, le_rfl, h⟩⟩
  let B (j : ι) := j.val.support
  have hB : Monotone B := fun _ _ h => h.choose
  let d := iSupCocone B hB
  let hd := isColimitISupCocone B hB
  let e : Cocone (diagram B hB) := {
    pt := X
    ι.app j := j.val.lift
    ι.naturality j k f := by
      change homOfLE (hB (leOfHom f)) ≫ k.val.lift = j.val.lift ≫ 𝟙 X
      rw [Category.comp_id]
      exact (leOfHom f).choose_spec }
  let l : toPresheaf (⨆ j, B j) ⟶ X := hd.desc e
  have hl (j : ι) : homOfLE (le_iSup B j) ≫ l = j.val.lift := hd.fac e j
  let hA : A ≤ ⨆ j, B j := j₀.val.le_support.trans (le_iSup B j₀)
  have hleft : homOfLE hA ≫ l = a := by
    have h : homOfLE hA = homOfLE j₀.val.le_support ≫ homOfLE (le_iSup B j₀) := by
      apply (cancel_mono (inclusion (⨆ j, B j))).1
      simp only [Category.assoc, homOfLE_inclusion]
    rw [h, Category.assoc, hl, j₀.val.lift_left]
  have hright : l ≫ p = inclusion (⨆ j, B j) ≫ b := by
    apply hd.hom_ext
    intro j
    change homOfLE (le_iSup B j) ≫ l ≫ p =
      homOfLE (le_iSup B j) ≫ inclusion (⨆ j, B j) ≫ b
    rw [← Category.assoc, hl, j.val.lift_right]
    exact (homOfLE_inclusion_assoc (le_iSup B j) b).symm
  let M : PartialLift P A a p b :=
    ⟨⨆ j, B j, hA, l, hleft, hright, hP B hB (fun j => j.val.le_support)
      (fun j => j.val.property)⟩
  exact ⟨M, fun N hN => ⟨le_iSup B (⟨N, hN⟩ : ι), hl ⟨N, hN⟩⟩⟩

/-- A sectionwise extension operation on intermediate subpresheaves gives
an actual lift, provided the predicate on the intermediate supports is
closed under directed unions. -/
theorem hasLiftingProperty_inclusion_of_extend_of_property
    (hA : P A)
    (hP : ∀ {ι : Type (max u v)} [Preorder ι] [IsFiltered ι]
      (B : ι → Subpresheaf Q), Monotone B → (∀ j, A ≤ B j) → (∀ j, P (B j)) → P (⨆ j, B j))
    (h : ∀ (B : Subpresheaf Q), A ≤ B → P B →
      ∀ (q : Cᵒᵖ × SimplexCategoryᵒᵖ) (s : (Functor.uncurry.obj Q).obj q),
        ∃ D : Subpresheaf Q, s ∈ D.obj q ∧ P (B ⊔ D) ∧
          HasLiftingProperty (homOfLE (inf_le_right : B ⊓ D ≤ D)) p) :
    HasLiftingProperty (inclusion A) p where
  sq_hasLift := by
    intro a b w
    let : Nonempty (PartialLift P A a p b) := ⟨initialPartialLift P w.w.symm hA⟩
    obtain ⟨M, hM⟩ := zorn_le_nonempty (α := PartialLift P A a p b)
      (fun c hc hn => partialLift_bddAbove P hP c hc hn)
    have htop : M.support = ⊤ := by
      apply top_unique
      intro q s _
      obtain ⟨D, hs, hNext, hLift⟩ := h M.support M.le_support M.property q s
      let sq₁ := isPushout_inf_sup M.support D
      let i := homOfLE (inf_le_right : M.support ⊓ D ≤ D)
      let j := homOfLE (le_sup_left : M.support ≤ M.support ⊔ D)
      have sq₂ : CommSq (homOfLE (inf_le_left : M.support ⊓ D ≤ M.support) ≫ M.lift)
          i p (inclusion D ≫ b) := ⟨by
        simp only [i, Category.assoc, M.lift_right, homOfLE_inclusion_assoc]⟩
      let : HasLiftingProperty i p := hLift
      let l := sq₁.desc M.lift sq₂.lift (by rw [sq₂.fac_left])
      have hl : j ≫ l = M.lift := sq₁.inl_desc _ _ _
      have hr : l ≫ p = inclusion (M.support ⊔ D) ≫ b := by
        apply sq₁.hom_ext
        · rw [← Category.assoc, hl, M.lift_right, homOfLE_inclusion_assoc]
        · rw [← Category.assoc, IsPushout.inr_desc, sq₂.fac_right, homOfLE_inclusion_assoc]
      let hAS : A ≤ M.support ⊔ D := M.le_support.trans le_sup_left
      have hc : homOfLE hAS = homOfLE M.le_support ≫ j := by
        apply (cancel_mono (inclusion (M.support ⊔ D))).1
        simp only [j, Category.assoc, homOfLE_inclusion]
      have hleft : homOfLE hAS ≫ l = a := by
        rw [hc, Category.assoc, hl, M.lift_left]
      let N : PartialLift P A a p b := ⟨M.support ⊔ D, hAS, l, hleft, hr, hNext⟩
      have hNM : N ≤ M := hM ⟨le_sup_left, hl⟩
      exact hNM.choose q ((le_sup_right : D ≤ M.support ⊔ D) q hs)
    let g := lift (𝟙 Q) (show Subfunctor.range (Functor.uncurry.map (𝟙 Q)) ≤ M.support from
      htop.symm ▸ le_top)
    have hg : g ≫ inclusion M.support = 𝟙 Q := lift_inclusion _ _
    have hga : inclusion A ≫ g = homOfLE M.le_support := by
      apply (cancel_mono (inclusion M.support)).1
      rw [Category.assoc, hg, Category.comp_id, homOfLE_inclusion]
    refine ⟨⟨{ l := g ≫ M.lift, fac_left := ?_, fac_right := ?_ }⟩⟩
    · rw [← Category.assoc, hga, M.lift_left]
    · rw [Category.assoc, M.lift_right, ← Category.assoc, hg, Category.id_comp]

/-- If any missing section can be covered by a weak intersection admitting
the given right lift, every square from the original weak inclusion lifts. -/
theorem hasLiftingProperty_inclusion_of_extend
    (hA : ∀ Φ : J.Point.{max u v},
      SSet.IsRealizationWeakEquivalence (Φ.presheafFiber.map (inclusion A)))
    (h : ∀ (B : Subpresheaf Q)
      (_ : ∀ Φ : J.Point.{max u v},
        SSet.IsRealizationWeakEquivalence (Φ.presheafFiber.map (inclusion B)))
      (q : Cᵒᵖ × SimplexCategoryᵒᵖ) (s : (Functor.uncurry.obj Q).obj q),
      ∃ D : Subpresheaf Q, s ∈ D.obj q ∧
        (∀ Φ : J.Point.{max u v}, SSet.IsRealizationWeakEquivalence
          (Φ.presheafFiber.map (homOfLE (inf_le_right : B ⊓ D ≤ D)))) ∧
        HasLiftingProperty (homOfLE (inf_le_right : B ⊓ D ≤ D)) p) :
    HasLiftingProperty (inclusion A) p := by
  let V (B : Subpresheaf Q) : Prop := ∃ h : A ≤ B, ∀ Φ : J.Point.{max u v},
    SSet.IsRealizationWeakEquivalence (Φ.presheafFiber.map (homOfLE h))
  apply hasLiftingProperty_inclusion_of_extend_of_property V
  · have e : homOfLE (le_rfl : A ≤ A) = 𝟙 _ := (cancel_mono (inclusion A)).1 (by simp)
    refine ⟨le_rfl, fun Φ => ?_⟩
    rw [e, Functor.map_id]
    exact SSet.IsRealizationWeakEquivalence.id _
  · intro ι _ _ B hB hAB hVB
    let j₀ : ι := Classical.choice IsFiltered.nonempty
    exact ⟨(hAB j₀).trans (le_iSup B j₀), fun Φ =>
      isRealizationWeakEquivalence_homOfLE_iSup B hB hAB j₀ Φ
        (fun j => (hVB j).choose_spec Φ)⟩
  · intro B hAB hVB q s
    have hWeak (Φ : J.Point.{max u v}) :
        SSet.IsRealizationWeakEquivalence (Φ.presheafFiber.map (inclusion B)) := by
      have hw : SSet.IsRealizationWeakEquivalence
          (Φ.presheafFiber.map (homOfLE hAB ≫ inclusion B)) := by
        rw [homOfLE_inclusion]
        exact hA Φ
      rw [Functor.map_comp] at hw
      exact SSet.IsRealizationWeakEquivalence.of_comp_left hw (hVB.choose_spec Φ)
    obtain ⟨D, hs, hd, hp⟩ := h B hWeak q s
    refine ⟨D, hs, ⟨hAB.trans le_sup_left, ?_⟩, hp⟩
    intro Φ
    let i := homOfLE (inf_le_right : B ⊓ D ≤ D)
    let : Mono i := mono_of_mono_fac (homOfLE_inclusion (inf_le_right : B ⊓ D ≤ D))
    let j := homOfLE (le_sup_left : B ≤ B ⊔ D)
    have hj := PointedSimplicialPresheaf.isRealizationWeakEquivalence_presheafFiber_of_isPushout
      C J Φ (isPushout_inf_sup B D).flip (hd Φ)
    have e : homOfLE (hAB.trans le_sup_left) = homOfLE hAB ≫ j :=
      (cancel_mono (inclusion (B ⊔ D))).1 (by simp only [j, Category.assoc, homOfLE_inclusion])
    rw [e, Functor.map_comp]
    exact hj.comp (hVB.choose_spec Φ)

end CategoryTheory.SimplicialSubpresheaf
