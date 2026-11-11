/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.CommonBoundaryGeometry
public import StacksFrontier.AlgebraicGeometry.Morphisms.CoproductImmersion

/-!
# Both whole boundaries are actual closed subschemes

Disjoint closed boundary components give a closed coproduct immersion by the
pinned native coproduct theorem. Both component maps are actual pullbacks. The
whole finite field boundary remains finite on the original product source.
Adapted from original EffectiveCartierDivisor/FullBoundaryProduct.lean and
RelativeCurve/Pencils/FactorBoundary.lean at motivic a6805c4.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

section Lambda

variable {S C Y D Z : Scheme.{u}} (q : C ⟶ S) (j : Y ⟶ C)
  (d : D ⟶ C) (s : Z ⟶ Y)

/-- Disjointness on C implies disjointness in the original relative product. -/
theorem fullGraphBoundary_disjoint (h : Disjoint (Set.range j) (Set.range d)) :
    Disjoint (Set.range (infinityProductMap q j d))
      (Set.range (markedProductMap q j s)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨a, rfl⟩ ⟨b, hb⟩
  have he := congrArg (fun x => (pullback.snd (j ≫ q) q) x) hb
  have ha := congrArg
    (fun v : pullback (pullback.snd (j ≫ q) q) d ⟶ C => v a)
    (pullback.condition (f := pullback.snd (j ≫ q) q) (g := d))
  have hb' : (pullback.snd (j ≫ q) q) (markedProductMap q j s b) =
      j (s (pullback.snd (j ≫ q) (s ≫ j ≫ q) b)) := by
    change (markedProductMap q j s ≫ pullback.snd (j ≫ q) q) b = _
    rw [markedProductMap, pullback.lift_snd]
    rfl
  exact Set.disjoint_iff_forall_ne.mp h ⟨_, rfl⟩ ⟨_, rfl⟩
    (hb'.symm.trans (he.trans ha))

/-- The scheme-theoretic union is an actual closed immersion into Y × C. -/
theorem fullGraphBoundary_isClosedImmersion [IsClosedImmersion d]
    [IsClosedImmersion (s ≫ j)] (h : Disjoint (Set.range j) (Set.range d)) :
    IsClosedImmersion (fullGraphBoundaryMap q j s d) := by
  have : IsClosedImmersion (markedProductMap q j s) :=
    MorphismProperty.of_isPullback (markedProductMap_isPullback q j s).flip inferInstance
  exact isClosedImmersion_coprodDesc _ _ (fullGraphBoundary_disjoint q j d s h)

/-- The infinity product projection is finite by actual pullback of the finite boundary. -/
theorem infinityProduct_isFinite [IsFinite (d ≫ q)] :
    IsFinite (infinityProductMap q j d ≫ pullback.fst (j ≫ q) q) := by
  have H := (IsPullback.of_hasPullback (pullback.snd (j ≫ q) q) d).paste_horiz
    (IsPullback.of_hasPullback (j ≫ q) q)
  exact MorphismProperty.of_isPullback H.flip inferInstance

/-- Finiteness of both original components gives finiteness of the whole relative boundary. -/
theorem fullGraphBoundary_isFinite [IsFinite (d ≫ q)] [IsFinite (s ≫ j ≫ q)] :
    IsFinite (fullGraphBoundaryMap q j s d ≫ pullback.fst (j ≫ q) q) := by
  have := infinityProduct_isFinite q j d
  have hz : markedProductMap q j s ≫ pullback.fst (j ≫ q) q =
      pullback.fst (j ≫ q) (s ≫ j ≫ q) := by
    exact pullback.lift_fst _ _ _
  have : IsFinite (markedProductMap q j s ≫ pullback.fst (j ≫ q) q) := by
    rw [hz]
    infer_instance
  dsimp only [fullGraphBoundaryMap]
  rw [coprod.desc_comp]
  infer_instance


end Lambda

variable {S X Y A Z C D V : Scheme.{u}}
  (q : X ⟶ S) (π : C ⟶ S) (j : Y ⟶ C) (p : Y ⟶ X)
  (hq : j ≫ π = p ≫ q) (a : A ⟶ X)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (d : D ⟶ C) 

lemma psiZeroInclusion_isPullback :
    IsPullback (pullback.snd (a ≫ q) (z ≫ q)) (psiZeroInclusion q π j p hq a z s hs)
      (s ≫ j) (pullback.snd (a ≫ q) π) := by
  have hz : (s ≫ j) ≫ π = z ≫ q := by rw [Category.assoc, hq, ← Category.assoc, hs]
  have H : IsPullback (pullback.snd (a ≫ q) (z ≫ q))
      (pullback.fst _ _) ((s ≫ j) ≫ π) (a ≫ q) := by
    rw [hz]
    exact (IsPullback.of_hasPullback _ _).flip
  convert H.of_bot' (IsPullback.of_hasPullback (a ≫ q) π).flip using 1
  apply pullback.hom_ext <;> simp [psiZeroInclusion]

lemma psiBoundary_closed [IsClosedImmersion d] [IsClosedImmersion (s ≫ j)]
    (hd : Disjoint (Set.range j) (Set.range d)) :
    IsClosedImmersion (psiBoundaryInclusion q π j p hq a z s hs d) := by
  have : IsClosedImmersion (psiZeroInclusion q π j p hq a z s hs) :=
    MorphismProperty.of_isPullback (psiZeroInclusion_isPullback q π j p hq a z s hs) inferInstance
  apply isClosedImmersion_coprodDesc
  apply Set.disjoint_left.mpr
  rintro x ⟨u, rfl⟩ ⟨w, hw⟩
  have h1 := congrArg (fun f => f u)
    (pullback.condition (f := pullback.snd (a ≫ q) π) (g := d))
  have h2 := congrArg (fun f => f w) (psiZeroInclusion_isPullback q π j p hq a z s hs).w
  have h3 := congrArg (fun t => (pullback.snd (a ≫ q) π) t) hw
  exact Set.disjoint_iff_forall_ne.mp hd ⟨_, rfl⟩ ⟨_, rfl⟩ (h2.trans (h3.trans h1))


end AlgebraicGeometry.Scheme.RelativeCurvePencil
