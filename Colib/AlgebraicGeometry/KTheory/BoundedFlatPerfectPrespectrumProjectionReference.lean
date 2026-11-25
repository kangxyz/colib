/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareMergedSimplex
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareProjection
public import Colib.KTheory.Waldhausen.Iterated.ModelReferenceReanchor

/-!
# The fixed original outer-projection reference of the H0 chart diagrams

Reanchor the actual merged rectangle without changing any vertex functor. The
common outer square uses the two literal projections, and the first three selected
source nodes retain their entire normalization references. Adapted from
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProjectionReferenceNodes.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectProjectionReference

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "N" => boundedAboveFlatPerfectNormalizedPullback
open BoundedFlatPerfectDoubleSquareMergedSimplex
open BoundedFlatPerfectDoubleSquareCommonSimplex
  (lastSourceIso lastRightRawReference lastRightNormalizedReference)

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (r : C ⟶ A) (r' : C' ⟶ A') (hr : q ≫ p = r) (hr' : q' ≫ p' = r')

/-- The binary normalization source for the outer projection composite `c ≫ r`. -/
abbrev reference := BoundedFlatPerfectBinarySimplex.sourceMap c r

include hr in
theorem anchor : (reference c r).hom.toFunctor =
    (BoundedFlatPerfectTripleSimplex.source c q p).hom.toFunctor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg N (congrArg (fun k ↦ c ≫ k) hr.symm))

/--
A model morphism equipped with a natural isomorphism from the fixed outer projection reference.
-/
abbrev Node := Σ F : asSmallCategory (W A) ⟶
    asSmallCategory (W C'), (reference c r).hom.toFunctor ≅ F.hom.toFunctor

/-- Change only the reference of every actual original rectangle node. -/
def nodes (i : Fin 18) : Node c r :=
  ModelSimplex.reanchorNodes (F₀ := reference c r)
    (F₁ := BoundedFlatPerfectTripleSimplex.source c q p) (eqToIso (anchor p q c r hr))
    (BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq) i

/--
The projection rectangle's model simplex reanchored at the outer projection reference using the
equation `hr`.
-/
def simplex : ModelSimplex (asSmallCategory (W A))
    (asSmallCategory (W C')) 17 :=
  ModelSimplex.reanchorSimplex (F₀ := reference c r)
    (F₁ := BoundedFlatPerfectTripleSimplex.source c q p) (eqToIso (anchor p q c r hr))
    (BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq)

/-- The entire original rectangle is unchanged by the explicit common reference transport. -/
theorem simplex_original : simplex p q p' q' a b c hp hq r hr =
    BoundedFlatPerfectDoubleSquareMergedSimplex.simplex p q p' q' a b c hp hq :=
  ModelSimplex.reanchorSimplex_eq (eqToIso (anchor p q c r hr))
    (BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq)

include hp hq hr hr' in
/-- The projection composites retain this actual transported target source. -/
theorem outerAnchor : (reference c r).hom.toFunctor =
    (BoundedFlatPerfectBinarySimplex.sourceMap r' a).hom.toFunctor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg N
      (DoubleSquareTrack.outer_eq p q p' q' a b c hp hq r r' hr hr'))

/-- Canonical five-node outer square, independent of any chart factorization. -/
def outerNodes (houter : c ≫ r = r' ≫ a) : Fin 5 → Node c r :=
  ![⟨reference c r, Iso.refl _⟩,
    ⟨BoundedFlatPerfectBinarySimplex.intermediateMap c r,
      BoundedFlatPerfectBinarySimplex.first c r⟩,
    ⟨BoundedFlatPerfectBinarySimplex.targetMap c r, BoundedFlatPerfectBinarySimplex.total c r⟩,
    ⟨BoundedFlatPerfectBinarySimplex.intermediateMap r' a,
      eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
        (congrArg N houter)) ≪≫
        BoundedFlatPerfectBinarySimplex.first r' a⟩,
    ⟨BoundedFlatPerfectBinarySimplex.targetMap r' a,
      eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
        (congrArg N houter)) ≪≫
        BoundedFlatPerfectBinarySimplex.total r' a⟩]

/-- The actual projection equations supply the common outer square's original reference. -/
def sharedNodes : Fin 5 → Node c r :=
  outerNodes a c r r' (DoubleSquareTrack.outer_eq p q p' q' a b c hp hq r r' hr hr')

/-- The five rectangle labels `0, 1, 2, 14, 15` selecting the common outer-square nodes. -/
def sharedIndex : Fin 5 → Fin 18 := ![0, 1, 2, 14, 15]

/-- The actual common source node is preserved with its reference. -/
theorem source_node : nodes p q p' q' a b c hp hq r hr 0 =
    sharedNodes p q p' q' a b c hp hq r r' hr hr' 0 := by
  subst r
  change (⟨reference c (q ≫ p), Iso.refl _ ≪≫ Iso.refl _⟩ : Node c (q ≫ p)) =
    ⟨reference c (q ≫ p), Iso.refl _⟩
  rw [Iso.refl_trans]

/-- The first original raw normalization intermediate is common. -/
theorem source_raw_node : nodes p q p' q' a b c hp hq r hr 1 =
    sharedNodes p q p' q' a b c hp hq r r' hr hr' 1 := by
  subst r
  change (⟨BoundedFlatPerfectBinarySimplex.intermediateMap c (q ≫ p),
    Iso.refl _ ≪≫ BoundedFlatPerfectBinarySimplex.first c (q ≫ p)⟩ : Node c (q ≫ p)) =
    ⟨BoundedFlatPerfectBinarySimplex.intermediateMap c (q ≫ p),
      BoundedFlatPerfectBinarySimplex.first c (q ≫ p)⟩
  rw [Iso.refl_trans]

/-- The first normalized endpoint is common. -/
theorem source_normal_node : nodes p q p' q' a b c hp hq r hr 2 =
    sharedNodes p q p' q' a b c hp hq r r' hr hr' 2 := by
  subst r
  change (⟨BoundedFlatPerfectBinarySimplex.targetMap c (q ≫ p),
    Iso.refl _ ≪≫ BoundedFlatPerfectBinarySimplex.total c (q ≫ p)⟩ : Node c (q ≫ p)) =
    ⟨BoundedFlatPerfectBinarySimplex.targetMap c (q ≫ p),
      BoundedFlatPerfectBinarySimplex.total c (q ≫ p)⟩
  rw [Iso.refl_trans]

/-- The projected raw target retains its original equality-transported reference. -/
theorem target_raw_reference : (nodes p q p' q' a b c hp hq r hr 14).2 =
    eqToIso (outerAnchor p q p' q' a b c hp hq r (q' ≫ p') hr rfl) ≪≫
      BoundedFlatPerfectBinarySimplex.first (q' ≫ p') a := by
  change eqToIso (anchor p q c r hr) ≪≫
    (lastSourceIso p q p' q' a b c hp hq ≪≫
      BoundedFlatPerfectSplitTripleSimplex.rightFirstGeometric q' p' a) = _
  rw [lastRightRawReference, ← Iso.trans_assoc, eqToIso_trans]

/-- The projected normalized target reference retains the original total normalization. -/
theorem target_normal_reference : (nodes p q p' q' a b c hp hq r hr 15).2 =
    eqToIso (outerAnchor p q p' q' a b c hp hq r (q' ≫ p') hr rfl) ≪≫
      BoundedFlatPerfectBinarySimplex.total (q' ≫ p') a := by
  change eqToIso (anchor p q c r hr) ≪≫
    (lastSourceIso p q p' q' a b c hp hq ≪≫
      BoundedFlatPerfectTripleSimplex.rightFirst q' p' a) = _
  rw [lastRightNormalizedReference, ← Iso.trans_assoc, eqToIso_trans]

theorem target_raw_map : (nodes p q p' q' a b c hp hq r hr 14).1 =
    BoundedFlatPerfectBinarySimplex.intermediateMap (q' ≫ p') a := by
  apply WideSubcategory.hom_ext
  exact CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext rfl

theorem target_normal_map : (nodes p q p' q' a b c hp hq r hr 15).1 =
    BoundedFlatPerfectBinarySimplex.targetMap (q' ≫ p') a := by
  apply WideSubcategory.hom_ext
  exact CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext rfl

/-- The full raw target node uses the actual target projection equation. -/
theorem target_raw_node : nodes p q p' q' a b c hp hq r hr 14 =
    sharedNodes p q p' q' a b c hp hq r r' hr hr' 3 := by
  subst r'
  apply Sigma.ext (target_raw_map p q p' q' a b c hp hq r hr)
  exact heq_of_eq (target_raw_reference p q p' q' a b c hp hq r hr)

/-- The full normalized target node uses the same actual target projection equation. -/
theorem target_normal_node : nodes p q p' q' a b c hp hq r hr 15 =
    sharedNodes p q p' q' a b c hp hq r r' hr hr' 4 := by
  subst r'
  apply Sigma.ext (target_normal_map p q p' q' a b c hp hq r hr)
  exact heq_of_eq (target_normal_reference p q p' q' a b c hp hq r hr)

/-- All five shared nodes retain their entire actual reference isomorphisms. -/
theorem shared_nodes (i : Fin 5) : nodes p q p' q' a b c hp hq r hr (sharedIndex i) =
    sharedNodes p q p' q' a b c hp hq r r' hr hr' i := by
  fin_cases i
  · exact source_node p q p' q' a b c hp hq r r' hr hr'
  · exact source_raw_node p q p' q' a b c hp hq r r' hr hr'
  · exact source_normal_node p q p' q' a b c hp hq r r' hr hr'
  · exact target_raw_node p q p' q' a b c hp hq r r' hr hr'
  · exact target_normal_node p q p' q' a b c hp hq r r' hr hr'

include hr' in
/-- Two actual chart factorizations share the full original outer-path nodes. -/
theorem two_projection_shared (q₂ : C ⟶ B) (q₂' : C' ⟶ B')
    (hq₂ : c ≫ q₂ = q₂' ≫ b) (hr₂ : q₂ ≫ p = r) (hr₂' : q₂' ≫ p' = r')
    (i : Fin 5) :
    nodes p q p' q' a b c hp hq r hr (sharedIndex i) =
      nodes p q₂ p' q₂' a b c hp hq₂ r hr₂ (sharedIndex i) :=
  (shared_nodes p q p' q' a b c hp hq r r' hr hr' i).trans
    (shared_nodes p q₂ p' q₂' a b c hp hq₂ r r' hr₂ hr₂' i).symm

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectProjectionReference
