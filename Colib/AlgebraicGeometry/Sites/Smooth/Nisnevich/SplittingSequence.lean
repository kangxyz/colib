/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.SimpleRefinement
import Colib.AlgebraicGeometry.Morphisms.Etale.Neighborhood.EtaleNeighborhoodFromClosedSection
import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen
import Colib.AlgebraicGeometry.Sites.Smooth.PullbackSquare

/-!
# Simple refinements from a finite Nisnevich splitting sequence

A splitting sequence for an actual morphism `q : Y ⟶ X` is recorded over
a chain of open immersions. On each complementary closed subscheme the
sequence provides a section of the pullback of `q`, expressed by its
original factorization equation. An étale neighborhood of that closed
section supplies the right leg of a geometric distinguished square.

See Voevodsky, [Unstable motivic homotopy categories in Nisnevich and
cdh-topologies](https://arxiv.org/abs/0805.4576), Definition 2.15 and Proposition 2.17.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}}

/-- A finite splitting sequence over a map into the base of the original cover. -/
inductive NisnevichSplittingSequence {X Y : SmoothSite S} (q : Y ⟶ X) :
    {V : SmoothSite S} → (V ⟶ X) → Prop
  | empty {V : SmoothSite S} (p : V ⟶ X) (hV : IsEmpty V.left) :
      NisnevichSplittingSequence q p
  | step {U V : SmoothSite S} (p : V ⟶ X) (i : U ⟶ V)
      (hi : IsOpenImmersion i.left) (hU : NisnevichSplittingSequence q (i ≫ p))
      {Z : Scheme.{u}} (z : Z ⟶ V.left) (hz : IsClosedImmersion z)
      (hcomp : Set.range z = (Set.range i.left)ᶜ)
      (s : Z ⟶ Y.left) (hs : s ≫ q.left = z ≫ p.left) :
      NisnevichSplittingSequence q p

variable [IsNoetherian S]

/-- A splitting sequence refines the pullback of a sieve if every arrow
factoring through the original cover admits a simple refinement of that sieve. -/
theorem NisnevichSplittingSequence.hasSimpleNisnevichRefinement
    {X Y : SmoothSite S} {q : Y ⟶ X} [Etale q.left] {V : SmoothSite S} {p : V ⟶ X}
    (hSplit : NisnevichSplittingSequence q p) (R : Sieve X)
    (hRight : ∀ ⦃W : SmoothSite S⦄ (f : W ⟶ Y),
      HasSimpleNisnevichRefinement IsGeometricNisnevichSquare W (R.pullback (f ≫ q))) :
    HasSimpleNisnevichRefinement IsGeometricNisnevichSquare V (R.pullback p) := by
  induction hSplit with
  | empty p hV => exact .empty hV
  | @step U V p i hi hU Z z hz hcomp s hs ih =>
    let : IsOpenImmersion i.left := hi
    let : IsClosedImmersion z := hz
    let T := pullback q p
    let πY : T ⟶ Y := pullback.fst q p
    let πV : T ⟶ V := pullback.snd q p
    have hpb : IsPullback πY.left πV.left q.left p.left :=
      (forgetScheme S).map_isPullback (IsPullback.of_hasPullback q p)
    let : Etale πV.left := MorphismProperty.of_isPullback hpb inferInstance
    let t : Z ⟶ T.left := hpb.lift s z hs
    have ht : t ≫ πV.left = z := hpb.lift_snd s z hs
    let c : Z ⟶ pullback πV.left z :=
      pullback.lift t (𝟙 Z) (by simpa only [Category.id_comp] using ht)
    have hc : c ≫ pullback.snd πV.left z = 𝟙 Z := pullback.lift_snd _ _ _
    obtain ⟨W, hW⟩ := Scheme.Hom.exists_open_iso_over_closed_of_section πV.left z c hc
    let E := (opensFunctor T).obj W
    let w : E ⟶ T := openInclusion T W
    let v : E ⟶ V := w ≫ πV
    let f : E ⟶ Y := w ≫ πY
    have hcomm : v ≫ p = f ≫ q := by
      change (w ≫ pullback.snd q p) ≫ p = (w ≫ pullback.fst q p) ≫ q
      simp only [Category.assoc, pullback.condition]
    let Q := ordinaryPullbackSquare i v
    have hQ : IsGeometricNisnevichSquare Q := by
      refine ⟨IsPullback.of_hasPullback i v, hi, ?_, ⟨Z, z, hz, hcomp, hW⟩⟩
      change Etale (W.ι ≫ πV.left)
      infer_instance
    refine HasSimpleNisnevichRefinement.square hQ ?_ ?_
    · change HasSimpleNisnevichRefinement IsGeometricNisnevichSquare U ((R.pullback p).pullback i)
      rw [← Sieve.pullback_comp]
      exact ih
    · change HasSimpleNisnevichRefinement IsGeometricNisnevichSquare E ((R.pullback p).pullback v)
      rw [← Sieve.pullback_comp, hcomm]
      exact hRight f

/-- A split étale arrow in a sieve gives a simple refinement of that sieve. -/
theorem hasSimpleNisnevichRefinement_of_mem_of_splittingSequence
    {X Y : SmoothSite S} {q : Y ⟶ X} [Etale q.left] {R : Sieve X}
    (hq : R q) (hSplit : NisnevichSplittingSequence q (𝟙 X)) :
    HasSimpleNisnevichRefinement IsGeometricNisnevichSquare X R := by
  have h := hSplit.hasSimpleNisnevichRefinement R (by
    intro W f
    exact HasSimpleNisnevichRefinement.pullback_of_mem (R.downward_closed hq f))
  simpa only [Sieve.pullback_id] using h

end AlgebraicGeometry.Scheme.SmoothSite
