/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartOriginalFixedInputs
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartCompactificationProjectivity
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartCompactifiedFullBoundary
public import Colib.AlgebraicGeometry.Sites.Smooth.NormalComponents
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodInductionSmallStageAction
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.OriginalFixedTargetRestriction

/-! # The original chart geometry consumed without replacing its refinement

The affine tail is presented by its original ring, not by a new isomorphic base.
Only original compactification and chart data are inputs. All geometric conditions
on the actual pullback compactification are derived below.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u v
namespace AlgebraicGeometry.Scheme.SmoothSite.EtaleChart
open OriginalFixed

/-- The native affine tail stays affine as an object of the smooth site.
This explicit local instance avoids repeatedly unfolding the bundled object
while elaborating the marked-neighborhood and strict-local-ring parameters. -/
local instance affine_native_tail
    {K : Type u} [Field K] {R : Type u} [CommRing R]
    (tail : Spec (.of R) ⟶ Spec (.of K))
    [Smooth tail] [IsSeparated tail] [QuasiCompact tail] :
    IsAffine (SmoothSite.mk tail).left :=
  inferInstanceAs (IsAffine (Spec (.of R)))

/-- The native original chart and its retraction become equal on one genuine
marked neighborhood, using the same original retained target and finite cover. -/
theorem exists_original_chart_restriction
    {K : Type u} [Field K] (P : PresheafWithTransfers.{v} K)
    (hP : PresheafWithTransfers.IsA1Invariant P)
    {R : Type u} [CommRing R]
    (tail : Spec (.of R) ⟶ Spec (.of K))
    [Smooth tail] [IsSeparated tail] [QuasiCompact tail]
    {A Z T : SmoothSite (Spec (.of K))} [IsAffine A.left] [IsAffine Z.left]
    (q : A ⟶ Z) [Etale q.left]
    (p : Z ⟶ SmoothSite.mk tail) [Smooth p.left]
    (s : SmoothSite.mk tail ⟶ Z) (hs : s.left ≫ p.left = 𝟙 _)
    {U N D E : Scheme.{u}} [IsAffine U] [IsNormal N] [IrreducibleSpace N]
    (i : A.left ⟶ U) (f : U ⟶ Spec (.of R))
    (hi : i ≫ f = q.left ≫ p.left) [hSmoothF : SmoothOfRelativeDimension 1 f]
    (j : U ⟶ N) [IsOpenImmersion j]
    (fN : N ⟶ Spec (.of R)) [IsProper fN] (hj : j ≫ fN = f)
    (d : D ⟶ N) [IsClosedImmersion d] [hFiniteD : IsFinite (d ≫ fN)]
    (hd : Set.range d = (Set.range j)ᶜ)
    (t : U ⟶ T.left) (ht : t ≫ T.hom = f ≫ tail)
    (π : N ⟶ projectiveLine R) [IsFinite π]
    (hπ : π ≫ (projectiveLine R ↘ Spec (.of R)) = fN)
    (aU : U ⟶ Spec (.of (Polynomial R)))
    (haU : aU ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
      j ≫ fN)
    (hjπ : j ≫ π = aU ≫ projectiveLineXChart R)
    (eChart : E ⟶ N) [IsOpenImmersion eChart] [Nonempty E]
    (aE : E ⟶ Spec (.of (Polynomial R))) [Etale aE]
    (haE : aE ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
      eChart ≫ fN)
    (heπ : eChart ≫ π = aE ≫ projectiveLineXChart R)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (ξ : Spec (.of Ω) ⟶ A.left) (η : Spec (.of Ω) ⟶ Spec (.of R))
    (hξ : ξ ≫ q.left = η ≫ s.left)
    (B : BigEtaleSite.{u}) (hX : B.Contains (refinementObject q p s).left)
    (i₀ : SmallEtaleNeighborhood (refinementObject q p s)
      (refinementGeometricPoint q p s ξ η hξ hs))
    (k : ℕ)
    (hn : ∀ (W : SmoothSite (Spec (.of K)))
      (z : PresheafWithTransfers.sections P ((Cor.graphFunctor K).obj W)), (k + 1) • z = 0)
    (hnUnit : IsUnit ((k + 1 : ℕ) : ↥(etaleLocalRing B
      (refinementObject q p s).left hX (refinementGeometricPoint q p s ξ η hξ hs)))) :
    ∃ Anew : EtaleNeighborhood (refinementObject q p s)
        (refinementGeometricPoint q p s ξ η hξ hs).hom,
      ((PresheafWithTransfers.toPresheaf K).obj P).map
        (etaleNeighborhoodHom _ _ Anew ≫ originalTarget q p s i f hi t ht).op =
      ((PresheafWithTransfers.toPresheaf K).obj P).map
        (etaleNeighborhoodHom _ _ Anew ≫ retractTarget q p s i f hi t ht).op := by
  let X := refinementObject q p s
  let x := refinementGeometricPoint q p s ξ η hξ hs
  let b : X.left ⟶ Spec (.of R) :=
    Scheme.EtaleChart.original q.left p.left s.left ≫ (q.left ≫ p.left)
  let C : Scheme := Scheme.EtaleChart.compactifiedCurve q.left p.left s.left fN
  let c : C ⟶ X.left := pullback.fst b fN
  let vC : C ⟶ N := pullback.snd b fN
  let V : Scheme := Scheme.EtaleChart.curve q.left p.left s.left f
  let jC : V ⟶ C := OriginalFixed.inclusion q p s f j fN hj
  let dC := Scheme.EtaleChart.compactifiedFullBoundaryMap q.left p.left s.left fN d
  let : IsNormal X.left := isNormal_overField K X
  let : IsLocallyNoetherian X.left := isLocallyNoetherian_overField K X
  let : IsNormal C := Scheme.EtaleChart.compactifiedCurve_isNormal
    q.left p.left s.left fN
  let : IsProper c := inferInstanceAs (IsProper (pullback.fst b fN))
  let : Flat vC := Scheme.EtaleChart.compactifiedCurve_toOriginal_flat
    q.left p.left s.left fN
  let : IsAffine V := Scheme.EtaleChart.curve_isAffine_of_affine_chart
    q.left p.left s.left f
  let : IsOpenImmersion jC := Scheme.EtaleChart.retainedToCompactification_isOpenImmersion
    q.left p.left s.left f j fN hj
  let : SmoothOfRelativeDimension 1 (jC ≫ c) :=
    @Scheme.EtaleChart.retainedToCompactification_structure_smoothOfRelativeDimension
      A.left (Spec (.of R)) Z.left U N
      q.left p.left s.left f j fN hj 1 hSmoothF
  let : IsClosedImmersion dC :=
    Scheme.EtaleChart.compactifiedFullBoundaryMap_isClosedImmersion
      q.left p.left s.left fN d
  let : IsFinite (dC ≫ c) := @Scheme.EtaleChart.compactifiedFullBoundaryMap_finite
    A.left (Spec (.of R)) Z.left N D
    q.left p.left s.left fN d hFiniteD
  have hdC := Scheme.EtaleChart.compactifiedFullBoundaryMap_complement
    q.left p.left s.left fN d f j hj hd
  have hp : IsProjectiveMorphism c :=
    Scheme.EtaleChart.compactifiedCurve_isProjective_of_finite_cover
      q.left p.left s.left fN π hπ
  exact exists_original_fixed_target_restriction P hP X x c jC dC hdC
    (originalSection q p s i f hi) (retractSection q p s i f hi hs)
    (originalSection_structure q p s i f hi j fN hj)
    (retractSection_structure q p s i f hi j fN hj hs)
    (sections_common_mark q p s i f hi j fN hj ξ η hξ hs)
    (retainedTarget q p s f t)
    (retainedTarget_over_base q p s f j fN hj t ht)
    (originalTarget q p s i f hi t ht) (retractTarget q p s i f hi t ht)
    (originalTarget_recovery q p s i f hi t ht)
    (retractTarget_recovery q p s i f hi t ht hs)
    vC fN b (IsPullback.of_hasPullback b fN).flip
    j (pullback.snd b f)
    (Scheme.EtaleChart.retainedToCompactification_isPullback
      q.left p.left s.left f j fN hj)
    π hπ aU haU hjπ eChart aE haE heπ B hX i₀ hp k hn hnUnit

end AlgebraicGeometry.Scheme.SmoothSite.EtaleChart
