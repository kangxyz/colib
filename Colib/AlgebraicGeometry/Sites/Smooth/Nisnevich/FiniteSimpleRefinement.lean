/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.FiniteCovers
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.SplittingSequence
import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen
import Colib.AlgebraicGeometry.Sites.Smooth.PullbackSquare

/-!
# Simple refinements of finite total Nisnevich covers

A map into the actual finite disjoint union splits its source into the
preimages of the summands. Two complementary preimages give a geometric
Nisnevich square, with each piece factoring through its original component.
Applied to a finite totalization, this constructs simple refinements over
every arrow factoring through the total map. The splitting sequence then
gives a simple refinement of the original covering sieve.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [IsNoetherian S]

private theorem exists_openPreimage_factor
    {A T W : SmoothSite S} (f : W ⟶ T) (i : A ⟶ T) [IsOpenImmersion i.left] :
    ∃ a : (opensFunctor W).obj (f.left ⁻¹ᵁ i.left.opensRange) ⟶ A,
      openInclusion W (f.left ⁻¹ᵁ i.left.opensRange) ≫ f = a ≫ i := by
  let U := f.left ⁻¹ᵁ i.left.opensRange
  let j := openInclusion W U
  have hRange : Set.range (j.left ≫ f.left) ⊆ Set.range i.left := by
    rintro _ ⟨x, rfl⟩
    have hx : j.left x ∈ U := by
      let x' : U := x
      change x'.val ∈ U
      exact x'.property
    exact hx
  let a₀ := IsOpenImmersion.lift i.left (j.left ≫ f.left) hRange
  have ha : a₀ ≫ i.left = j.left ≫ f.left := IsOpenImmersion.lift_fac _ _ _
  let a : (opensFunctor W).obj U ⟶ A := homMk a₀ (by
    rw [← MorphismProperty.Over.w i, ← Category.assoc, ha, Category.assoc,
      MorphismProperty.Over.w f, MorphismProperty.Over.w j])
  refine ⟨a, ?_⟩
  apply MorphismProperty.Over.Hom.ext
  exact ha.symm

/-- The actual preimages of the components of a finite disjoint union give
a simple refinement whenever their maps lie in the specified sieve. -/
theorem hasSimpleNisnevichRefinement_of_finiteCoproduct
    {n : ℕ} (Y : Fin n → SmoothSite S) {W : SmoothSite S} (f : W ⟶ finiteCoproduct Y)
    (R : Sieve W)
    (h : ∀ (i : Fin n) ⦃Z : SmoothSite S⦄ (j : Z ⟶ W) (a : Z ⟶ Y i),
      j ≫ f = a ≫ finiteCoproductι Y i → R j) :
    HasSimpleNisnevichRefinement IsGeometricNisnevichSquare W R := by
  induction n generalizing W with
  | zero =>
    let : IsEmpty (finiteCoproduct Y).left := inferInstanceAs (IsEmpty (∅ : Scheme.{u}))
    exact .empty ⟨fun x ↦ isEmptyElim (f.left x)⟩
  | succ n ih =>
    let Y' : Fin n → SmoothSite S := fun i ↦ Y i.succ
    let A := Y 0
    let B := finiteCoproduct Y'
    let iA := coproductInl A B
    let iB := coproductInr A B
    let f' : W ⟶ coproduct A B := f
    let U := f'.left ⁻¹ᵁ iA.left.opensRange
    let V := f'.left ⁻¹ᵁ iB.left.opensRange
    let l := openInclusion W U
    let r := openInclusion W V
    obtain ⟨a, ha⟩ := exists_openPreimage_factor f' iA
    obtain ⟨b, hb⟩ := exists_openPreimage_factor f' iB
    let : IsOpenImmersion l.left := inferInstanceAs (IsOpenImmersion U.ι)
    let : IsOpenImmersion r.left := inferInstanceAs (IsOpenImmersion V.ι)
    have hcomp : Set.range r.left = (Set.range l.left)ᶜ := by
      change Set.range V.ι = (Set.range U.ι)ᶜ
      rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      change f'.left ⁻¹' (Set.range iB.left) = (f'.left ⁻¹' (Set.range iA.left))ᶜ
      have hCompl : Set.range iB.left = (Set.range iA.left)ᶜ :=
        (isCompl_range_inl_inr A.left B.left).symm.eq_compl
      rw [hCompl, Set.preimage_compl]
    have hClosed : IsClosedImmersion r.left := by
      apply IsClosedImmersion.of_isPreimmersion
      rw [hcomp]
      exact l.left.isOpenEmbedding.isOpen_range.isClosed_compl
    let Q := ordinaryPullbackSquare l r
    have hQ : IsGeometricNisnevichSquare Q :=
      ⟨IsPullback.of_hasPullback l r, inferInstance, inferInstance,
        ⟨_, r.left, hClosed, hcomp, inferInstance⟩⟩
    refine HasSimpleNisnevichRefinement.square hQ ?_ ?_
    · exact HasSimpleNisnevichRefinement.pullback_of_mem (h 0 l a ha)
    · refine ih Y' b (R.pullback r) ?_
      intro i Z j c hc
      change R (j ≫ r)
      apply h i.succ (j ≫ r) c
      change (j ≫ r) ≫ f' = c ≫ (finiteCoproductι Y' i ≫ iB)
      change r ≫ f' = b ≫ iB at hb
      rw [Category.assoc, hb, ← Category.assoc, hc, Category.assoc]

/-- Pulling back a sieve along any arrow through a finite normalized total
cover gives a simple refinement by its selected original components. -/
theorem FiniteNisnevichCoverNormalization.hasSimpleNisnevichRefinement_pullback
    {X : SmoothSite S} {ι : Type v} {Y : ι → SmoothSite S} {f : ∀ i, Y i ⟶ X}
    (N : FiniteNisnevichCoverNormalization f) (R : Sieve X)
    (hR : ∀ i : Fin N.size, R (f (N.index i))) {W : SmoothSite S} (w : W ⟶ N.total) :
    HasSimpleNisnevichRefinement IsGeometricNisnevichSquare W (R.pullback (w ≫ N.map)) := by
  apply hasSimpleNisnevichRefinement_of_finiteCoproduct _ w _
  intro i Z j a hj
  change R (j ≫ w ≫ N.map)
  change j ≫ w = a ≫ N.inclusion i at hj
  rw [← Category.assoc, hj, Category.assoc, N.inclusion_map]
  exact R.downward_closed (hR i) a

/-- Actual splitting sequences of the singleton covers imply completeness
of the geometric Nisnevich squares on the smooth site. -/
theorem nisnevichSimpleRefinements_of_splittingSequences
    (hSplit : ∀ {X Y : SmoothSite S} (q : Y ⟶ X),
      Presieve.singleton q.left ∈ _root_.AlgebraicGeometry.Nisnevich.precoverage X.left →
      NisnevichSplittingSequence q (𝟙 X)) :
    NisnevichSimpleRefinements (S := S) IsGeometricNisnevichSquare := by
  intro X R hR
  obtain ⟨P, hP, hPR⟩ := mem_nisnevichTopology_iff.mp hR
  obtain ⟨ι, Y, f, rfl⟩ := P.exists_eq_ofArrows
  rw [mem_nisnevichPrecoverage_iff, Presieve.map_ofArrows] at hP
  change Presieve.ofArrows (fun i ↦ (Y i).left) (fun i ↦ (f i).left) ∈
    _root_.AlgebraicGeometry.Nisnevich.precoverage X.left at hP
  let N := normalizeFiniteNisnevichCoverOfMem f hP
  have hN := (hSplit N.map N.mem_precoverage).hasSimpleNisnevichRefinement R (by
    intro W w
    exact N.hasSimpleNisnevichRefinement_pullback R (fun i ↦ hPR _ _ (.mk (N.index i))) w)
  simpa only [Sieve.pullback_id] using hN

end AlgebraicGeometry.Scheme.SmoothSite
