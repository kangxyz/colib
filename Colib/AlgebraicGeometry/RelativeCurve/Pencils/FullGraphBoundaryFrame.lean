/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.MarkedGraphFrame
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.CanonicalBoundaryFrame
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.DisjointBoundaryGluing

/-!
# The actual graph frame on the entire infinity-plus-marked boundary

The infinity frame is the inverse of the genuine canonical graph section. The
marked frame is produced by the entire polynomial Cartesian square, including
where its polynomial coordinate vanishes. Their coproduct frame is glued with
exact component restrictions. Neither component frame nor its canonical-section
coordinate is an additional hypothesis.

This combines the native replacements of the original `FullBoundaryFrames.lean`
and `FullBoundaryCoordinate.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

variable {S C Y D : Scheme.{u}} (q : C ⟶ S) [IsSeparated q]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))

/-- The entire inverse image of the infinity boundary in the actual product. -/
abbrev infinityProductMap :
    pullback (pullback.snd (j ≫ q) q) d ⟶ pullback (j ≫ q) q :=
  pullback.fst (pullback.snd (j ≫ q) q) d

include hd in
omit [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)] in
/-- The actual infinity product is disjoint from the whole compactification graph. -/
theorem compactificationGraph_disjoint_infinity :
    Disjoint (Set.range (infinityProductMap q j d))
      ((compactificationGraph q j).ker.support : Set (pullback (j ≫ q) q : Scheme)) := by
  apply relativeGraph_disjoint_boundary (j ≫ q) q j rfl (infinityProductMap q j d)
  rw [infinityProductMap, pullback.condition]
  apply Set.disjoint_left.2
  rintro x ⟨w, rfl⟩ hx
  exact Set.disjoint_left.1 hd hx ⟨pullback.snd (pullback.snd (j ≫ q) q) d w, rfl⟩

/-- The infinity graph-line frame is derived from the actual canonical section. -/
def compactificationInfinityDivisorFrame :
    (Modules.pullback (infinityProductMap q j d)).obj
      (divisorSheaf (compactificationGraph q j).ker) ≅
        SheafOfModules.unit (pullback (pullback.snd (j ≫ q) q) d).ringCatSheaf :=
  canonicalDisjointBoundaryFrame (compactificationGraph q j).ker
    (infinityProductMap q j d) (compactificationGraph_disjoint_infinity q j d hd)

@[simp]
theorem compactificationInfinityDivisorFrame_coordinate :
    (compactificationInfinityDivisorFrame q j d hd).hom.app ⊤
      (pullbackGlobalSections (infinityProductMap q j d)
        (divisorSheaf (compactificationGraph q j).ker)
        (divisorSheafGlobalSection (compactificationGraph q j).ker)) =
          (1 : Γ((pullback (pullback.snd (j ≫ q) q) d : Scheme), ⊤)) :=
  canonicalDisjointBoundaryFrame_coordinate _ _ _

/-- The literal whole boundary, with both unreduced components retained. -/
abbrev fullGraphBoundaryMap {S C Y Z D : Scheme.{u}} (q : C ⟶ S)
    (j : Y ⟶ C) (s : Z ⟶ Y) (d : D ⟶ C) :=
  coprod.desc (infinityProductMap q j d) (markedProductMap q j s)

section PolynomialMark

variable (R B : Type u) [CommRing R] [CommRing B] (z : Polynomial R →+* B)
  {C Y D : Scheme.{u}} (q : C ⟶ Spec (.of R)) [IsSeparated q]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
  (p : Y ⟶ Spec (.of (Polynomial R)))
  (hq : j ≫ q = p ≫ coordinateLineProjection R)
  (s : Spec (.of B) ⟶ Y) (hs : s ≫ p = coordinateMark R B z)
  (H : IsPullback s (𝟙 (Spec (.of B))) p (coordinateMark R B z))
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))

/-- Both component frames are genuine constructions, so the whole-boundary
frame and its literal restrictions require no supplied frame hypothesis. -/
theorem exists_fullGraphDivisorFrame :
    ∃ E : (Modules.pullback (fullGraphBoundaryMap q j s d)).obj
        (divisorSheaf (compactificationGraph q j).ker) ≅
          SheafOfModules.unit
            ((pullback (pullback.snd (j ≫ q) q) d) ⨿
              pullback (j ≫ q) (s ≫ j ≫ q)).ringCatSheaf,
      (Modules.restrictFunctor (coprod.inl :
        pullback (pullback.snd (j ≫ q) q) d ⟶ _)).map E.hom ≫
          (Modules.restrictUnitIso _).hom =
        (boundaryCoprodRestrictLeft (infinityProductMap q j d)
          (markedProductMap q j s)).hom.app _ ≫
            (compactificationInfinityDivisorFrame q j d hd).hom ∧
      (Modules.restrictFunctor (coprod.inr :
        pullback (j ≫ q) (s ≫ j ≫ q) ⟶ _)).map E.hom ≫
          (Modules.restrictUnitIso _).hom =
        (boundaryCoprodRestrictRight (infinityProductMap q j d)
          (markedProductMap q j s)).hom.app _ ≫
            (compactificationMarkedDivisorFrame R B z q j p hq s hs H).hom :=
  exists_boundaryCoprod_frame (infinityProductMap q j d) (markedProductMap q j s)
    (divisorSheaf (compactificationGraph q j).ker)
    (compactificationInfinityDivisorFrame q j d hd)
    (compactificationMarkedDivisorFrame R B z q j p hq s hs H)

/-- A chosen actual frame of the unchanged full graph boundary. -/
def fullGraphDivisorFrame :=
  Classical.choose (exists_fullGraphDivisorFrame R B z q j p hq s hs H d hd)

/-- The literal coordinate of the canonical section in the chosen full frame. -/
def fullGraphCanonicalCoordinate :
    Γ(((pullback (pullback.snd (j ≫ q) q) d) ⨿
      pullback (j ≫ q) (s ≫ j ≫ q) : Scheme.{u}), ⊤) :=
  (fullGraphDivisorFrame R B z q j p hq s hs H d hd).hom.app ⊤
    (pullbackGlobalSections (fullGraphBoundaryMap q j s d)
      (divisorSheaf (compactificationGraph q j).ker)
      (divisorSheafGlobalSection (compactificationGraph q j).ker))

/-- In the actual left-component comparison, the canonical section has coordinate one. -/
theorem fullGraphDivisorFrame_infinity_coordinate :
    ((Modules.restrictFunctor (coprod.inl :
        pullback (pullback.snd (j ≫ q) q) d ⟶ _)).map
          (fullGraphDivisorFrame R B z q j p hq s hs H d hd).hom ≫
        (Modules.restrictUnitIso _).hom).app ⊤
      (((boundaryCoprodRestrictLeft (infinityProductMap q j d)
          (markedProductMap q j s)).app (divisorSheaf (compactificationGraph q j).ker)).inv.app ⊤
        (pullbackGlobalSections (infinityProductMap q j d)
          (divisorSheaf (compactificationGraph q j).ker)
          (divisorSheafGlobalSection (compactificationGraph q j).ker))) =
            (1 : Γ((pullback (pullback.snd (j ≫ q) q) d : Scheme), ⊤)) := by
  let e := (boundaryCoprodRestrictLeft (infinityProductMap q j d)
    (markedProductMap q j s)).app (divisorSheaf (compactificationGraph q j).ker)
  let σ := pullbackGlobalSections (infinityProductMap q j d)
    (divisorSheaf (compactificationGraph q j).ker)
    (divisorSheafGlobalSection (compactificationGraph q j).ker)
  have hr := (Classical.choose_spec
    (exists_fullGraphDivisorFrame R B z q j p hq s hs H d hd)).1
  have hframe := congrArg (fun m => Modules.Hom.app m ⊤ (e.inv.app ⊤ σ)) hr
  have he := congrArg (fun m => Modules.Hom.app m ⊤ σ) e.inv_hom_id
  exact hframe.trans ((congrArg (fun t =>
    (compactificationInfinityDivisorFrame q j d hd).hom.app ⊤ t) he).trans
    (compactificationInfinityDivisorFrame_coordinate q j d hd))

/-- In the actual right-component comparison, the canonical coordinate is exactly
the signed polynomial difference, including its whole zero scheme. -/
theorem fullGraphDivisorFrame_marked_coordinate :
    ((Modules.restrictFunctor (coprod.inr :
        pullback (j ≫ q) (s ≫ j ≫ q) ⟶ _)).map
          (fullGraphDivisorFrame R B z q j p hq s hs H d hd).hom ≫
        (Modules.restrictUnitIso _).hom).app ⊤
      (((boundaryCoprodRestrictRight (infinityProductMap q j d)
          (markedProductMap q j s)).app (divisorSheaf (compactificationGraph q j).ker)).inv.app ⊤
        (pullbackGlobalSections (markedProductMap q j s)
          (divisorSheaf (compactificationGraph q j).ker)
          (divisorSheafGlobalSection (compactificationGraph q j).ker))) =
      markedGraphCoordinate R B z q j p hq s hs := by
  let e := (boundaryCoprodRestrictRight (infinityProductMap q j d)
    (markedProductMap q j s)).app (divisorSheaf (compactificationGraph q j).ker)
  let σ := pullbackGlobalSections (markedProductMap q j s)
    (divisorSheaf (compactificationGraph q j).ker)
    (divisorSheafGlobalSection (compactificationGraph q j).ker)
  have hr := (Classical.choose_spec
    (exists_fullGraphDivisorFrame R B z q j p hq s hs H d hd)).2
  have hframe := congrArg (fun m => Modules.Hom.app m ⊤ (e.inv.app ⊤ σ)) hr
  have he := congrArg (fun m => Modules.Hom.app m ⊤ σ) e.inv_hom_id
  exact hframe.trans ((congrArg (fun t =>
    (compactificationMarkedDivisorFrame R B z q j p hq s hs H).hom.app ⊤ t) he).trans
    (compactificationMarkedDivisorFrame_coordinate R B z q j p hq s hs H))

end PolynomialMark

end AlgebraicGeometry.Scheme.RelativeCurvePencil
