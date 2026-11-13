/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.BoundedEnlargement
public import Colib.CategoryTheory.Sites.Simplicial.DirectedUnion
public import Colib.Topology.Realization.FiniteStrictLifting
import Colib.CategoryTheory.Sites.Simplicial.ReducedConeContraction

/-!
# Bounded trivial inverse images

Iterate the bounded enlargement countably many times. A finite
subcomplex of the union's fiber is already represented in one stage.
The next stage supplies its exact relative lift. This is the bounded
cofibration argument of Jardine, *Simplicial presheaves*, Lemma 2.4,
pp. 65–66. https://doi.org/10.1016/0022-4049(87)90100-9
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology
open scoped Simplicial Topology unitInterval

universe t w v u

namespace CategoryTheory.SimplicialSubpresheaf

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C} {P Q : Cᵒᵖ ⥤ SSet.{w}} (f : P ⟶ Q)

private theorem mono_fiber_map (Φ : J.Point.{w})
    {X Y : Cᵒᵖ ⥤ SSet.{w}} (g : X ⟶ Y) [Mono g] : Mono (Φ.presheafFiber.map g) := by
  let E := Φ.presheafFiber (A := SSet.{w})
  let hE : PreservesFiniteLimits E := inferInstanceAs
    (PreservesFiniteLimits (Φ.presheafFiber (A := SSet.{w})))
  let : PreservesLimitsOfShape WalkingCospan E := hE.preservesFiniteLimits WalkingCospan
  let : PreservesLimit (cospan g g) E := PreservesLimitsOfShape.preservesLimit
  exact preserves_mono_of_preservesLimit E g

omit [LocallySmall.{w} C] in
private theorem preimageMap_mono [Mono f] (A : Subpresheaf Q) : Mono (preimageMap A f) :=
  PullbackCone.mono_fst_of_is_pullback_of_mono (preimage_isPullback A f).isLimit

/-- Given a bounded starting subpresheaf, there is a bounded larger one
such that the original inverse image inclusion is weak on every point of
the specified bounded family. -/
theorem exists_bounded_trivial_preimage [Mono f]
    {ι : Type*} (point : ι → J.Point.{w}) (A : Subpresheaf Q)
    (hf : ∀ i, SSet.IsRealizationWeakEquivalence ((point i).presheafFiber.map f))
    (κ : Cardinal.{t}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (hI : HasCardinalLT ι κ) (hA : HasBoundedSections A κ)
    (hC : ∀ q : Cᵒᵖ × SimplexCategoryᵒᵖ,
      HasCardinalLT (Σ r : Cᵒᵖ × SimplexCategoryᵒᵖ, q ⟶ r) κ)
    (hPoint : ∀ i (U : C), HasCardinalLT ((point i).fiber.obj U) κ) :
    ∃ D : Subpresheaf Q, A ≤ D ∧ HasBoundedSections D κ ∧
      ∀ i, SSet.IsRealizationWeakEquivalence ((point i).presheafFiber.map (preimageMap D f)) := by
  let S := {B : Subpresheaf Q // HasBoundedSections B κ}
  have hs (B : S) := exists_bounded_enlargement_of_weakEquivalences
    f point B.val hf κ hκ hI B.property hC hPoint
  let next (B : S) : S := ⟨(hs B).choose, (hs B).choose_spec.choose_spec.1⟩
  let hNext (B : S) : B.val ≤ (next B).val := (hs B).choose_spec.choose
  let stages (n : ℕ) : S := Nat.rec ⟨A, hA⟩ (fun _ B => next B) n
  let B (n : ℕ) : Subpresheaf Q := (stages n).val
  have hB : Monotone B := monotone_nat_of_le_succ (fun n => hNext (stages n))
  let D := ⨆ n, B n
  have hNat : HasCardinalLT ℕ κ := by
    simpa only [HasCardinalLT, Cardinal.mk_nat, Cardinal.lift_aleph0,
      Cardinal.lift_id'.{0, t}] using hκ
  have hD : HasBoundedSections D κ :=
    Subfunctor.hasCardinalLT_totalSections_iSup B κ hNat (fun n => (stages n).property)
  refine ⟨D, le_iSup B 0, hD, ?_⟩
  intro i
  let E := (point i).presheafFiber (A := SSet.{w})
  let d := iSupCocone B hB
  have hd := isColimitISupCocone B hB
  let e := E.mapCocone d
  let : PreservesColimitsOfSize.{0, 0} E := preservesSmallestColimits_of_preservesColimits E
  have he : IsColimit e := isColimitOfPreserves E hd
  let : Mono (preimageMap D f) := preimageMap_mono f D
  let : Mono (E.map (preimageMap D f)) := mono_fiber_map (point i) (preimageMap D f)
  change SSet.IsRealizationWeakEquivalence (E.map (preimageMap D f))
  apply SSet.isRealizationWeakEquivalence_of_finiteSubcomplex_lifting
  intro K hK
  let : SSet.Finite K := hK
  let hKi : K.toSSet ⟶ e.pt := K.ι
  let : Fact Cardinal.aleph0.{w}.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  let : IsCardinalPresentable K.toSSet Cardinal.aleph0.{w} :=
    inferInstanceAs (IsFinitelyPresentable.{w} K.toSSet)
  let : EssentiallySmall.{w} ℕ := EssentiallySmall.mk' (AsSmall.equiv : ℕ ≌ AsSmall.{w} ℕ)
  let : IsCardinalFiltered ℕ Cardinal.aleph0.{w} :=
    (isCardinalFiltered_aleph0_iff ℕ).2 inferInstance
  obtain ⟨n, g', hg'⟩ := IsCardinalPresentable.exists_hom_of_isColimit
    (κ := Cardinal.aleph0.{w}) he hKi
  let B₀ := B n
  let B₁ := B (n + 1)
  let g : K.toSSet ⟶ E.obj (toPresheaf B₀) := g'
  have hg : g ≫ E.map (homOfLE (le_iSup B n)) = K.ι := by
    dsimp only [e, d, iSupCocone, Functor.mapCocone, Cocone.functoriality, hKi] at hg'
    exact hg'
  let L := SSet.Subcomplex.range g
  have hL : SSet.Finite L := inferInstanceAs (SSet.Finite (SSet.Subcomplex.range g))
  let h₀₁ : B₀ ≤ B₁ := hNext (stages n)
  let h₁D : B₁ ≤ D := le_iSup B (n + 1)
  let q₀ := preimageMap B₁ f
  let q₁ := preimageMap D f
  let incl := homOfLE h₁D
  let mapPre := homOfLE (show preimage B₁ f ≤ preimage D f from fun p _ h => h₁D p h)
  have hu : mapPre ≫ inclusion (preimage D f) = inclusion (preimage B₁ f) := homOfLE_inclusion _
  have eqPre : q₀ ≫ incl = mapPre ≫ q₁ := by
    apply (cancel_mono (inclusion D)).1
    simp only [Category.assoc, homOfLE_inclusion, preimageMap_inclusion, q₀, q₁, incl]
    rw [← Category.assoc, hu]
  have sq : IsPullback q₀ mapPre incl q₁ := by
    refine IsPullback.of_bot ?_ eqPre (preimage_isPullback D f)
    simpa only [hu, homOfLE_inclusion, incl, q₀] using preimage_isPullback B₁ f
  let hEL : PreservesFiniteLimits E := inferInstanceAs
    (PreservesFiniteLimits ((point i).presheafFiber (A := SSet.{w})))
  let : PreservesLimitsOfShape WalkingCospan E := hEL.preservesFiniteLimits WalkingCospan
  let : Mono (homOfLE h₁D) := mono_of_mono_fac (homOfLE_inclusion h₁D)
  let : Mono (E.map incl) := mono_fiber_map (point i) incl
  have hRange := SSet.realization_range_intersection_of_isPullback (sq.map E)
  obtain ⟨r₀, H₀, hH₀⟩ := (hs (stages n)).choose_spec.choose_spec.2 i L hL
  let g₀ := SSet.toTop.map (SSet.Subcomplex.toRange g)
  let incl₀ := SSet.toTop.map (L.ι ≫ E.map (homOfLE h₀₁))
  have hg₀ : g₀ ≫ incl₀ ≫ SSet.toTop.map (E.map incl) = SSet.toTop.map K.ι := by
    have hgι : SSet.Subcomplex.toRange g ≫ L.ι = g := SSet.Subcomplex.toRange_ι g
    have h : homOfLE h₀₁ ≫ incl = homOfLE (le_iSup B n) := by
      apply (cancel_mono (inclusion D)).1
      change (homOfLE h₀₁ ≫ homOfLE h₁D) ≫ inclusion D =
        homOfLE (le_iSup B n) ≫ inclusion D
      rw [Category.assoc, homOfLE_inclusion h₁D, homOfLE_inclusion h₀₁,
        homOfLE_inclusion (le_iSup B n)]
    dsimp only [g₀, incl₀]
    rw [← Functor.map_comp, ← Functor.map_comp]
    simp only [Category.assoc, reassoc_of% hgι, ← Functor.map_comp, h]
    exact congrArg SSet.toTop.map hg
  have hw : (SSet.toTop.map (E.map q₀)) ≫ SSet.toTop.map (E.map incl) =
      SSet.toTop.map (E.map mapPre) ≫ SSet.toTop.map (E.map q₁) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, eqPre]
  let r : C(|(K : SSet.{w})|, |E.obj (toPresheaf (preimage D f))|) :=
    ((SSet.toTop.map (E.map mapPre)).hom.comp r₀).comp g₀.hom
  let H₁ := (ContinuousMap.Homotopy.refl (SSet.toTop.map (E.map incl)).hom).comp H₀
  let H₂ := ContinuousMap.Homotopy.compContinuousMap H₁ g₀.hom
  have hleft :
      ((SSet.toTop.map (E.map incl)).hom.comp ((SSet.toTop.map (E.map q₀)).hom.comp r₀)).comp
        g₀.hom = (SSet.toTop.map (E.map q₁)).hom.comp r := by
    ext x
    exact ConcreteCategory.congr_hom hw (r₀ (g₀ x))
  have hright : ((SSet.toTop.map (E.map incl)).hom.comp incl₀.hom).comp g₀.hom =
      (SSet.toTop.map K.ι).hom := by
    ext x
    exact ConcreteCategory.congr_hom hg₀ x
  let H : ((SSet.toTop.map (E.map q₁)).hom.comp r).Homotopy (SSet.toTop.map K.ι).hom :=
    H₂.cast hleft hright
  refine ⟨r, H, ?_⟩
  intro t x hx
  have hrange : incl₀ (g₀ x) ∈ Set.range (SSet.toTop.map (E.map q₀)) := by
    have h : SSet.toTop.map (E.map incl) (incl₀ (g₀ x)) ∈
        Set.range (SSet.toTop.map (E.map q₀ ≫ E.map incl)) := by
      rw [hRange]
      exact ⟨⟨incl₀ (g₀ x), rfl⟩, (ConcreteCategory.congr_hom hg₀ x).symm ▸ hx⟩
    obtain ⟨y, hy⟩ := h
    refine ⟨y, (SSet.realization_mono_isClosedEmbedding (E.map incl)).injective ?_⟩
    change (SSet.toTop.map (E.map q₀) ≫ SSet.toTop.map (E.map incl)) y =
      SSet.toTop.map (E.map incl) (incl₀ (g₀ x))
    rwa [← Functor.map_comp]
  exact (congrArg (SSet.toTop.map (E.map incl)) (hH₀ t (g₀ x) hrange)).trans
    (ConcreteCategory.congr_hom hg₀ x)

end CategoryTheory.SimplicialSubpresheaf
