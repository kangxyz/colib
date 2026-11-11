/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeGraphDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.PointSectionCartier
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The full marked-product graph square and its native Cartier ideal

The compactification is only separated. Smoothness of relative dimension one is
required on the retained open curve. The complete marked scheme and its Cartesian
square are retained; no reduction, dense-open replacement, or graph disjointness
is used.

The explicit squares are adapted from
`Motivic/Aglib/AlgebraicGeometry/EffectiveCartierDivisor/GraphBoundaryRestriction.lean:27-80`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- The kernel ideal of a genuine base-change square of a closed immersion. -/
theorem ker_eq_comap_of_cartesian {A B X Y : Scheme.{u}} {i : A ⟶ X} {j : B ⟶ Y}
    [IsClosedImmersion i] {g : B ⟶ A} {f : Y ⟶ X} (H : IsPullback j g f i) :
    j.ker = i.ker.comap f := by
  rw [← H.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

variable {S C Y Z : Scheme.{u}} (q : C ⟶ S) (j : Y ⟶ C) (z : Z ⟶ Y)

/-- The unchanged native graph of the retained open in its compactification. -/
abbrev compactificationGraph : Y ⟶ pullback (j ≫ q) q :=
  relativeGraph (j ≫ q) q j rfl

/-- Restriction of the second factor to the specified entire boundary. -/
def markedProductMap : pullback (j ≫ q) (z ≫ j ≫ q) ⟶ pullback (j ≫ q) q :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ z ≫ j)
    (by simpa only [Category.assoc] using
      (pullback.condition (f := j ≫ q) (g := z ≫ j ≫ q)))

/-- The graph of the original boundary inclusion in the retained open. -/
def markedProductGraph : Z ⟶ pullback (j ≫ q) (z ≫ j ≫ q) :=
  pullback.lift z (𝟙 Z) (by simp)

/-- The ambient restriction is genuinely Cartesian. -/
theorem markedProductMap_isPullback :
    IsPullback (markedProductMap q j z) (pullback.snd (j ≫ q) (z ≫ j ≫ q))
      (pullback.snd (j ≫ q) q) (z ≫ j) where
  w := by simp [markedProductMap]
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun t ↦ by
    have hc : (t.fst ≫ pullback.fst (j ≫ q) q) ≫ (j ≫ q) =
        t.snd ≫ (z ≫ j ≫ q) := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, t.condition]
      simp only [Category.assoc]
    refine ⟨pullback.lift (t.fst ≫ pullback.fst (j ≫ q) q) t.snd hc,
      ?_, pullback.lift_snd _ _ _, ?_⟩
    · change pullback.lift (t.fst ≫ pullback.fst (j ≫ q) q) t.snd hc ≫
        markedProductMap q j z = t.fst
      apply pullback.hom_ext
      · simp [markedProductMap]
      · simpa [markedProductMap] using t.condition.symm
    · intro v hv hw
      change v ≫ markedProductMap q j z = t.fst at hv
      change v ≫ pullback.snd (j ≫ q) (z ≫ j ≫ q) = t.snd at hw
      apply pullback.hom_ext (f := j ≫ q) (g := z ≫ j ≫ q)
      · have he := congrArg (fun r ↦ r ≫ pullback.fst (j ≫ q) q) hv
        simpa [markedProductMap] using he
      · simpa using hw)⟩

/-- Restriction of the original compactification graph is the literal boundary graph. -/
theorem compactificationGraphMarked_isPullback [Mono j] :
    IsPullback z (markedProductGraph q j z) (compactificationGraph q j)
      (markedProductMap q j z) where
  w := by apply pullback.hom_ext <;> simp [markedProductGraph,
    compactificationGraph, relativeGraph, markedProductMap]
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun t ↦ by
    have hf : t.fst = t.snd ≫ pullback.fst (j ≫ q) (z ≫ j ≫ q) := by
      have he := congrArg (fun r ↦ r ≫ pullback.fst (j ≫ q) q) t.condition
      simpa [compactificationGraph, relativeGraph, markedProductMap] using he
    have hz : (t.snd ≫ pullback.snd (j ≫ q) (z ≫ j ≫ q)) ≫ z = t.fst := by
      apply (cancel_mono j).mp
      have he := congrArg (fun r ↦ r ≫ pullback.snd (j ≫ q) q) t.condition
      simpa [compactificationGraph, relativeGraph, markedProductMap] using he.symm
    refine ⟨t.snd ≫ pullback.snd (j ≫ q) (z ≫ j ≫ q), hz, ?_, ?_⟩
    · change (t.snd ≫ pullback.snd (j ≫ q) (z ≫ j ≫ q)) ≫
        markedProductGraph q j z = t.snd
      apply pullback.hom_ext
      · simpa [markedProductGraph] using hz.trans hf
      · simp [markedProductGraph]
    · intro v _ hv
      let v' : t.pt ⟶ Z := v
      have hv' : v' ≫ markedProductGraph q j z = t.snd := hv
      have he := congrArg (fun r ↦ r ≫ pullback.snd (j ≫ q) (z ≫ j ≫ q)) hv'
      have h : v' = t.snd ≫ pullback.snd (j ≫ q) (z ≫ j ≫ q) := by
        simpa only [markedProductGraph, Category.assoc, pullback.lift_snd,
          Category.comp_id] using he
      exact h)⟩


instance compactificationGraph_isClosedImmersion [IsSeparated q] :
    IsClosedImmersion (compactificationGraph q j) := inferInstance

instance markedProductGraph_isClosedImmersion [IsSeparated q] [IsOpenImmersion j] :
    IsClosedImmersion (markedProductGraph q j z) := by
  have : IsClosedImmersion
      (markedProductGraph q j z ≫ pullback.snd (j ≫ q) (z ≫ j ≫ q)) := by
    simpa only [markedProductGraph, pullback.lift_snd] using
      (inferInstance : IsClosedImmersion (𝟙 Z))
  exact IsClosedImmersion.of_comp _ (pullback.snd (j ≫ q) (z ≫ j ≫ q))

/-- The restriction retains the actual kernel ideal, not just its support. -/
theorem compactificationGraphIdeal_comap_markedProductMap [IsSeparated q]
    [IsOpenImmersion j] :
    (compactificationGraph q j).ker.comap (markedProductMap q j z) =
      (markedProductGraph q j z).ker :=
  (ker_eq_comap_of_cartesian (compactificationGraphMarked_isPullback q j z).flip).symm

/-- The marked graph is a section of the smooth retained curve over the entire mark scheme. -/
instance markedProductGraphIdeal_isEffectiveCartierDivisor [IsSeparated q]
    [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)] :
    IsEffectiveCartierDivisor (markedProductGraph q j z).ker := by
  have : SmoothOfRelativeDimension 1 (pullback.snd (j ≫ q) (z ≫ j ≫ q)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback (j ≫ q) (z ≫ j ≫ q)) inferInstance
  exact Stacks.Hilbert.isEffectiveCartierDivisor_ker_section
    (f := pullback.snd (j ≫ q) (z ≫ j ≫ q)) (markedProductGraph q j z)
      (by simp [markedProductGraph])

/-- The graph ideal is Cartier on the whole compactification product. Only its
retained open neighbourhood is assumed smooth. -/
theorem compactificationGraphIdeal_isEffectiveCartierDivisor [IsSeparated q]
    [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)] :
    IsEffectiveCartierDivisor (compactificationGraph q j).ker := by
  have hbase : IsOpenImmersion (𝟙 Y ≫ j) := inferInstance
  have hopen : IsOpenImmersion (markedProductMap q j (𝟙 Y)) :=
    MorphismProperty.of_isPullback (markedProductMap_isPullback q j (𝟙 Y)).flip hbase
  apply Stacks.Chow.isEffectiveCartierDivisor_of_comap_of_isOpenImmersion
    (compactificationGraph q j).ker (markedProductMap q j (𝟙 Y))
  · change ((compactificationGraph q j).ker.support :
      Set (pullback (j ≫ q) q : Scheme)) ⊆ _
    rw [Scheme.Hom.support_ker,
      (IsClosedImmersion.isClosedEmbedding (compactificationGraph q j)).isClosed_range.closure_eq]
    rintro _ ⟨y, rfl⟩
    refine ⟨markedProductGraph q j (𝟙 Y) y, ?_⟩
    have hw := (compactificationGraphMarked_isPullback q j (𝟙 Y)).w
    simpa only [Category.id_comp, Scheme.Hom.comp_apply] using
      congrArg (fun f => f y) hw.symm
  · rw [compactificationGraphIdeal_comap_markedProductMap]
    infer_instance

end AlgebraicGeometry.Scheme.RelativeCurvePencil
