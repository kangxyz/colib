/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartRetainedCompactificationGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleBoundaryDiagram

/-! # Full original boundary on the actual chart compactification

The boundary is the full scheme-theoretic base change of the original boundary,
with the same original chart refinement as the compactified and retained curves.
No compatibility, finiteness or complement certificate for the new curve is assumed.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleChart

variable {A Y Z U N D : Scheme.{u}}
  (q : A ⟶ Z) (p : Z ⟶ Y) (s : Y ⟶ Z)
  (fN : N ⟶ Y) (d : D ⟶ N)

/-- The unchanged original full boundary pulled back to the chart refinement. -/
abbrev compactifiedFullBoundary :=
  pullback (original q p s ≫ (q ≫ p)) (d ≫ fN)

/-- The actual native base-change inclusion into the same compactified curve. -/
def compactifiedFullBoundaryMap :
    compactifiedFullBoundary q p s fN d ⟶ compactifiedCurve q p s fN :=
  SmoothSite.etaleBoundaryBaseChangeMap (original q p s ≫ (q ≫ p)) fN d

/-- Both projections form the actual Cartesian square over the original boundary. -/
theorem compactifiedFullBoundaryMap_isPullback :
    IsPullback (compactifiedFullBoundaryMap q p s fN d)
      (pullback.snd (original q p s ≫ (q ≫ p)) (d ≫ fN))
      (pullback.snd (original q p s ≫ (q ≫ p)) fN) d :=
  SmoothSite.etaleBoundaryBaseChangeMap_isPullback (original q p s ≫ (q ≫ p)) fN d

@[reassoc (attr := simp)] theorem compactifiedFullBoundaryMap_structure :
    compactifiedFullBoundaryMap q p s fN d ≫
      pullback.fst (original q p s ≫ (q ≫ p)) fN =
    pullback.fst (original q p s ≫ (q ≫ p)) (d ≫ fN) :=
  SmoothSite.etaleBoundaryBaseChangeMap_fst (original q p s ≫ (q ≫ p)) fN d

instance compactifiedFullBoundaryMap_isClosedImmersion [IsClosedImmersion d] :
    IsClosedImmersion (compactifiedFullBoundaryMap q p s fN d) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (compactifiedFullBoundaryMap_isPullback q p s fN d).flip inferInstance

/-- Finiteness concerns the entire original boundary, not its reduced support. -/
theorem compactifiedFullBoundaryMap_finite [hfin : IsFinite (d ≫ fN)] :
    IsFinite (compactifiedFullBoundaryMap q p s fN d ≫
      pullback.fst (original q p s ≫ (q ≫ p)) fN) := by
  have hfst : IsFinite (pullback.fst (original q p s ≫ (q ≫ p)) (d ≫ fN)) :=
    MorphismProperty.of_isPullback (P := @IsFinite)
      (IsPullback.of_hasPullback (original q p s ≫ (q ≫ p)) (d ≫ fN)).flip hfin
  exact (congrArg IsFinite (compactifiedFullBoundaryMap_structure q p s fN d)).mpr hfst

/-- The actual full boundary is precisely the complement of the actual retained
inclusion, even when the base-changed compactification is reducible. -/
theorem compactifiedFullBoundaryMap_complement
    (f : U ⟶ Y) (j : U ⟶ N) (hj : j ≫ fN = f)
    (hd : Set.range d = (Set.range j)ᶜ) :
    Set.range (compactifiedFullBoundaryMap q p s fN d) =
      (Set.range (retainedToCompactification q p s f j fN hj))ᶜ := by
  have range_pb {P X Y S : Scheme.{u}}
      {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
      (hp : IsPullback a b f g) : Set.range a = f ⁻¹' Set.range g := by
    rw [← hp.isoPullback_hom_fst]
    change Set.range (pullback.fst f g ∘ hp.isoPullback.hom) = _
    rw [Set.range_comp, hp.isoPullback.hom.surjective.range_eq, Set.image_univ,
      Scheme.Pullback.range_fst]
  rw [range_pb (compactifiedFullBoundaryMap_isPullback q p s fN d),
    range_pb (retainedToCompactification_isPullback q p s f j fN hj), hd]
  rfl

/-- The three original full-boundary properties on the literal chart objects. -/
theorem compactifiedFullBoundary_geometry
    [IsClosedImmersion d] [IsFinite (d ≫ fN)]
    (f : U ⟶ Y) (j : U ⟶ N) (hj : j ≫ fN = f)
    (hd : Set.range d = (Set.range j)ᶜ) :
    IsClosedImmersion (compactifiedFullBoundaryMap q p s fN d) ∧
      IsFinite (compactifiedFullBoundaryMap q p s fN d ≫
        pullback.fst (original q p s ≫ (q ≫ p)) fN) ∧
      Set.range (compactifiedFullBoundaryMap q p s fN d) =
        (Set.range (retainedToCompactification q p s f j fN hj))ᶜ :=
  ⟨inferInstance, compactifiedFullBoundaryMap_finite q p s fN d,
    compactifiedFullBoundaryMap_complement q p s fN d f j hj hd⟩

end AlgebraicGeometry.Scheme.EtaleChart
