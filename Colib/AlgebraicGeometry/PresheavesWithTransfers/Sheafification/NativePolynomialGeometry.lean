/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.AffineLine.Open.FiniteMarkPuncture
public import Colib.AlgebraicGeometry.AffineLine.Open.OriginalRefinement
public import Colib.AlgebraicGeometry.Morphisms.Smooth.PolynomialProjection
public import Colib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.CommonCoefficientOpen
public import Colib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.FreePolynomialRestriction
public import Colib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.PairedBoundary
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.PairedSectionCylinderLifting
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.Representatives.NativePolynomial
public import Colib.AlgebraicGeometry.ProjectiveLine.AffineParameter
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.FiniteProjectiveAmple
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PolynomialMarkFrame
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.WholeCylinderGeometry
public import Colib.AlgebraicGeometry.Sites.Smooth.AffineLine.CylinderRestriction
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothOfRelativeDimension

/-!
# Lifting the original two representatives in polynomial coordinates

The normalization, its two free charts, and the whole boundary are chosen
over one coefficient open. A second coefficient open gives the two section
pairs. Both choices keep the original cylinder parameter and representatives.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Ample Stacks.Divisors Stacks.Morphisms
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.PolynomialLaurent
open _root_.AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
open _root_.AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine
open _root_.AlgebraicGeometry.Scheme.RelativeCurvePencil
open _root_.AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction
open scoped Polynomial

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

section ResidualBoundary

variable {S X Y P C Z D : Scheme.{u}} (q : X ⟶ S) (V : S.Opens)
  (π : P ⟶ S) (f : C ⟶ P) [IsFinite f]
  (j : Y ⟶ C) (jA : X ⟶ P) [IsOpenImmersion jA]
  (p : Y ⟶ X) (hRet : j ≫ f = p ≫ jA)
  (hB : j ≫ (f ≫ π) = p ≫ q) (hA : jA ≫ π = (𝟙 X) ≫ q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (d : D ⟶ C)

local notation "f'" => (sourceBaseMap π V f)
local notation "π'" => (compactificationProjection π V)
local notation "j'" => (firstInclusion q ⊤ V (f ≫ π) j p hB)
local notation "jA'" => (targetInclusion q V π jA hA)
local notation "p'" => (firstMap q ⊤ V p)
local notation "z'" => (markToParameter q ⊤ V z (fun _ _ ↦ trivial))
local notation "s'" => (closedLift q ⊤ V z (fun _ _ ↦ trivial) p s hs)
local notation "d'" => (sourceBaseMap (f ≫ π) V d)
local notation "Hslice" => (closedLift_isPullback q ⊤ V z (fun _ _ ↦ trivial) p s hs H)
local notation "hRet'" => (firstInclusion_comp_coefficientMap q V π jA hA f j p hRet hB)
local notation "hmark" => (markedSection_original_equation f j (z ≫ jA) s
  (pairedMark_isPullback f j jA p hRet z s H))
local notation "hmark'" => (markedSection_original_equation f' j' (z' ≫ jA') s'
  (pairedMark_isPullback f' j' jA' p' hRet' z' s' Hslice))

set_option maxHeartbeats 600000 in
-- The refined residual map and its chart restrictions have dependent scheme domains.
private theorem exists_refined_residual_factor_family
    (bE : (residualMarkedFiberOpen f j (z ≫ jA) s hmark).toScheme ⟶ D)
    (hbE : bE ≫ d = residualMarkedFiberMap f j (z ≫ jA) s hmark) :
    ∃ bE' : (residualMarkedFiberOpen f' j' (z' ≫ jA') s' hmark').toScheme ⟶
        (sourceBaseOpen (f ≫ π) V d).toScheme,
      bE' ≫ d' = residualMarkedFiberMap f' j' (z' ≫ jA') s' hmark' ∧
      ∀ (K : Scheme.{u}) (w : K ⟶ pullback (j' ≫ f' ≫ π') π'),
        PairedNormChartResidualFactor π' f' j' jA' p' hRet' z' s' Hslice w d' := by
  obtain ⟨bE', hbE'⟩ := exists_refined_residualBoundary_factor q V π f j jA p hRet hB hA
    z s hs H d bE hbE
  exact ⟨bE', hbE', pairedNormChart_residual_factor_family π' f' j' jA' p' hRet'
    z' s' Hslice d' bE' hbE'⟩

end ResidualBoundary

variable {k : Type u} [Field k] (R : Type u) [CommRing R] [IsDomain R]
  [IsIntegrallyClosed R] [IsNoetherianRing R] [Algebra k R] [Algebra.FiniteType k R]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]

local notation "q" => (polynomialProjection (.of R))
local notation "π" => (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
local notation "proj" => projection (SmoothSite.additiveGroupObject (Spec (.of k)))

local instance : SmoothOfRelativeDimension 1 q :=
  AffineLineEtaleCompactification.polynomialProjection_smooth_one R
local instance : Smooth q := SmoothOfRelativeDimension.smooth 1 q

set_option maxHeartbeats 1200000 in
-- The proof pastes both coefficient refinements of the actual compactification.
/-- Lift matching sections on the original representatives after the two
actual coefficient restrictions of their chosen native polynomial model. -/
theorem nativePolynomialRepresentativeLifting_of_pairedSectionCylinderLifting
    (lift : PairedSectionCylinderLifting k)
    (Pst : PresheafWithTransfers.{u + 1} k) (hPst : Pst.IsA1Invariant) :
    NativePolynomialRepresentativeLifting R t Pst := by
  intro X U T Ao Yo Bo jU _ l₀ _ eT m₀ H₀ i v bA bY HB A Y Z _ _ a _ p _ z _ _
    s hs H hcomp rA₀ rY₀ hA₀ hY₀ σ sA sY hm hsA hsY
  let : IsAffineHom p := isAffineHom_of_isAffine p
  let : IsAffineHom a := isAffineHom_of_isAffine a
  let f := toProjectiveLine R p
  let j := inclusion R p
  let jA := chart R
  let iInfinity := RelativeCurve.NativeProjectiveLine.infinity R
  have hRet : j ≫ f = p ≫ jA := inclusion_toProjectiveLine R p
  have hB : j ≫ (f ≫ π) = p ≫ q := inclusion_projection R p
  have hA : jA ≫ π = (𝟙 _) ≫ q := (chart_projection R).trans (Category.id_comp q).symm
  let : IsFinite f := toProjectiveLine_finite R p k
  let : IsAffine Z := isAffine_of_isAffineHom (z ≫ q)
  let frame := affineMarkPolynomialBoundaryGraphFrame R z
  have hcover₀ (x : Spec (.of R[X])) : x ∈ Set.range a ∨ x ∈ Set.range z := by
    by_cases hx : x ∈ Set.range a
    · exact Or.inl hx
    · exact Or.inr (by rwa [hcomp])
  have ha₀ : Disjoint (Set.range a) (Set.range z) := by
    rw [hcomp]
    exact disjoint_compl_right
  have hPuncture₀ := surjective_puncture_polynomialProjection_of_finite_mark R a z hcover₀
  obtain ⟨r, -, hfree, O, hO, hηO, hOr, hfinite⟩ := exists_common_coefficient_open
    R k p (polynomialCharts R)
  let : IsAffine O.toScheme := hO
  let xO : O.toScheme := ⟨genericPoint (Spec (.of R)), hηO⟩
  let q₁ := parameterProjection q ⊤ O
  let F₁ := sourceBaseMap π O f
  let π₁ := compactificationProjection π O
  let jB₁ := firstInclusion q ⊤ O (f ≫ π) j p hB
  let jA₁ := targetInclusion q O π jA hA
  let p₁ := firstMap q ⊤ O p
  let a₁ := secondMap q ⊤ O a
  let z₁ := markToParameter q ⊤ O z (fun _ _ ↦ trivial)
  let s₁ := closedLift q ⊤ O z (fun _ _ ↦ trivial) p s hs
  let hs₁ := closedLift_parameter q ⊤ O z (fun _ _ ↦ trivial) p s hs
  let H₁ := closedLift_isPullback q ⊤ O z (fun _ _ ↦ trivial) p s hs H
  let dA₁ := sourceBaseMap π O iInfinity
  have hF₁ : F₁ ≫ π₁ = compactificationProjection (f ≫ π) O :=
    sourceBaseMap_projection π O f
  have hF₁' : F₁ = f ∣_ (π ⁻¹ᵁ O) := by
    apply (cancel_mono (π ⁻¹ᵁ O).ι).1
    exact (sourceBaseMap_original π O f).trans (morphismRestrict_ι f (π ⁻¹ᵁ O)).symm
  let : IsFiniteLocallyFree F₁ := by
    rw [hF₁']
    exact finiteLocallyFree_restrict_of_free_polynomialCharts R f r hfree O hOr
  have hB₁ : jB₁ ≫ (F₁ ≫ π₁) = p₁ ≫ q₁ := by
    rw [hF₁]
    exact firstInclusion_projection q ⊤ O (f ≫ π) j p hB
  let hA₁ := targetInclusion_projection q O π jA hA
  let hRet₁ := firstInclusion_comp_coefficientMap q O π jA hA f j p hRet hB
  let ha₁ := puncture_disjoint q ⊤ O z (fun _ _ ↦ trivial) a ha₀
  have hcover₁ := puncture_cover q ⊤ O z (fun _ _ ↦ trivial) a hcover₀
  let : IsAffine (parameterOpen q ⊤ O).toScheme :=
    parameterOpen_affine q ⊤ O (isAffineOpen_top _) hO
  let : IsAffine (firstSource q ⊤ O p) := isAffine_of_isAffineHom p₁
  let : IsAffine (secondSource q ⊤ O a) := isAffine_of_isAffineHom a₁
  let : IsFinite (z₁ ≫ q₁) := markToParameter_finite q ⊤ O z (fun _ _ ↦ trivial)
  let frame₁ := canonicalGraphFrame q ⊤ O z (fun _ _ ↦ trivial) (by
    exact ((Modules.restrictFunctor _).mapIso frame) ≪≫ Modules.restrictUnitIso _)
  have hPuncture₁ := secondMap_surjective_base q O a hPuncture₀
  have hInfinity₁ : (Set.range jA₁)ᶜ ⊆ Set.range dA₁ :=
    targetInclusion_boundary_cover_top q O π jA hA iInfinity (range_infinity R).ge
  let : Surjective (iInfinity ≫ π) := by rw [infinity_projection]; infer_instance
  let : IsFinite (iInfinity ≫ π) := by rw [infinity_projection]; infer_instance
  let : Surjective (dA₁ ≫ π₁) := inferInstanceAs (Surjective (sourceBaseMap π O iInfinity ≫ π₁))
  let : IsFinite (dA₁ ≫ π₁) := by
    change IsFinite (sourceBaseMap π O iInfinity ≫ compactificationProjection π O)
    rw [sourceBaseMap_projection]
    infer_instance
  obtain ⟨D, d, hclosed, hd, hdisj, hsClosed, hzClosed, hfin, bI, bE, hbI, hbE⟩ :=
    exists_pairedBoundary_on_coefficientOpen R p z s hs H O hfinite
  let := hclosed
  let := hsClosed
  let := hzClosed
  let : IsFinite (d ≫ (F₁ ≫ π₁)) := by rw [hF₁]; exact hfin
  let L := finiteProjectiveCoefficient R 1 f
  let M := finiteProjectiveCoefficient R 1 (𝟙 (projectiveSpaceOverRing 1 (.of R)))
  let L₁ := coefficientModule (f ≫ π) O L
  let M₁ := coefficientModule π O M
  have hL₁ := coefficientModule_isAmple (f ≫ π) O hO L
    (finiteProjectiveCoefficient_isAmple R 1 f)
  have hM₁ := coefficientModule_isAmple π O hO M
    (finiteProjectiveCoefficient_isAmple R 1 (𝟙 (projectiveSpaceOverRing 1 (.of R))))
  have hDisj₁ : Disjoint (Set.range jA₁) (Set.range dA₁) :=
    targetInclusion_disjoint q O π jA hA iInfinity (by
      rw [range_infinity]
      exact disjoint_compl_right)
  obtain ⟨c, hx, -, e, ⟨cB, cA⟩⟩ := exists_pairedSectionData_on_coefficientOpen
    q₁ jB₁ p₁ hB₁ jA₁ hA₁ a₁ z₁ s₁ hs₁ H₁ d hdisj dA₁ hDisj₁ ha₁
    frame₁ L₁ hL₁ M₁ hM₁ ⊤ xO trivial
  let V := O.toScheme.basicOpen c
  let hV := (isAffineOpen_top O.toScheme).basicOpen c
  let : IsAffine V.toScheme := hV
  let q₂ := parameterProjection q₁ ⊤ V
  let F₂ := sourceBaseMap π₁ V F₁
  let π₂ := compactificationProjection π₁ V
  let jB₂ := firstInclusion q₁ ⊤ V (F₁ ≫ π₁) jB₁ p₁ hB₁
  let jA₂ := targetInclusion q₁ V π₁ jA₁ hA₁
  let p₂ := firstMap q₁ ⊤ V p₁
  let a₂ := secondMap q₁ ⊤ V a₁
  let z₂ := markToParameter q₁ ⊤ V z₁ (fun _ _ ↦ trivial)
  let s₂ := closedLift q₁ ⊤ V z₁ (fun _ _ ↦ trivial) p₁ s₁ hs₁
  let hs₂ := closedLift_parameter q₁ ⊤ V z₁ (fun _ _ ↦ trivial) p₁ s₁ hs₁
  let H₂ := closedLift_isPullback q₁ ⊤ V z₁ (fun _ _ ↦ trivial) p₁ s₁ hs₁ H₁
  let dB₂ := sourceBaseMap (F₁ ≫ π₁) V d
  let dA₂ := sourceBaseMap π₁ V dA₁
  have hF₂ : F₂ ≫ π₂ = compactificationProjection (F₁ ≫ π₁) V :=
    sourceBaseMap_projection π₁ V F₁
  have hB₂₀ : jB₂ ≫ compactificationProjection (F₁ ≫ π₁) V = p₂ ≫ q₂ :=
    firstInclusion_projection q₁ ⊤ V (F₁ ≫ π₁) jB₁ p₁ hB₁
  have hB₂ : jB₂ ≫ (F₂ ≫ π₂) = p₂ ≫ q₂ := by
    rw [hF₂]
    exact hB₂₀
  let hA₂ := targetInclusion_projection q₁ V π₁ jA₁ hA₁
  let hRet₂ := firstInclusion_comp_coefficientMap q₁ V π₁ jA₁ hA₁
    F₁ jB₁ p₁ hRet₁ hB₁
  let ha₂ := puncture_disjoint q₁ ⊤ V z₁ (fun _ _ ↦ trivial) a₁ ha₁
  let hdB₂ := refinedInfinity_disjoint q₁ ⊤ V (F₁ ≫ π₁) jB₁ p₁ hB₁ d hdisj
  let hdA₂ := targetInclusion_disjoint q₁ V π₁ jA₁ hA₁ dA₁ hDisj₁
  let : SmoothOfRelativeDimension 1 (jB₂ ≫ F₂ ≫ π₂) := by rw [hF₂]; infer_instance
  obtain ⟨bI₂, hbI₂⟩ :=
    exists_sourceBaseMap_inverseBoundary_factor π₁ V F₁ d dA₁ bI hbI
  obtain ⟨bE₂, hbE₂, hResidual⟩ := exists_refined_residual_factor_family q₁ V π₁ F₁
    jB₁ jA₁ p₁ hRet₁ hB₁ hA₁ z₁ s₁ hs₁ H₁ d bE hbE
  have hSrc : SourceMarkedBoundaryGeneration π₂ F₂ jB₂ (z₂ ≫ jA₂) s₂ dB₂ :=
    sourceMarkedBoundaryGeneration_of_residualFactor π₂ F₂ jB₂ jA₂ p₂ hRet₂
      z₂ s₂ hs₂ H₂ dB₂ bE₂ hbE₂
  let c₁ := SectionData.changeProjection q₂ hF₂.symm jB₂ p₂ hB₂₀ hB₂
    a₂ z₂ s₂ hs₂ H₂ e dB₂ hdB₂ ha₂ cB
  let c₂ := cA
  let : IsClosedImmersion (z₂ ≫ jA₂) := by rw [targetInclusion_mark]; infer_instance
  have hcover₂ := puncture_cover q₁ ⊤ V z₁ (fun _ _ ↦ trivial) a₁ hcover₁
  have hd₂ : (Set.range jB₂)ᶜ ⊆ Set.range dB₂ := by
    rw [firstInclusion_range_preimage_top, sourceBaseMap_range_preimage, hd]
    exact Set.Subset.rfl
  have hInfinity₂ := targetInclusion_boundary_cover_top q₁ V π₁
    jA₁ hA₁ dA₁ hInfinity₁
  have hcoverA := target_puncture_boundary_cover jA₂ a₂ z₂ dA₂ hInfinity₂ hcover₂
  let u₂ := pullback.fst p₂ a₂
  let v₂ := u₂ ≫ jB₂
  let g₂ := pullback.snd p₂ a₂
  have hvg : v₂ ≫ F₂ = g₂ ≫ (a₂ ≫ jA₂) := by
    calc
      _ = u₂ ≫ (jB₂ ≫ F₂) := Category.assoc _ _ _
      _ = (u₂ ≫ p₂) ≫ jA₂ := (congrArg (u₂ ≫ ·) hRet₂).trans (Category.assoc _ _ _).symm
      _ = (g₂ ≫ a₂) ≫ jA₂ := congrArg (· ≫ jA₂) pullback.condition
      _ = _ := Category.assoc _ _ _
  have hcoverB := source_overlap_boundary_cover jB₂ p₂ a₂ z₂ s₂ H₂ dB₂ hd₂ hcover₂
  have hPuncture₂ := secondMap_surjective_base q₁ V a₁ hPuncture₁
  have hPunctureA : Function.Surjective ((a₂ ≫ jA₂) ≫ π₂) := by
    rwa [Category.assoc, hA₂, Category.id_comp]
  let xV : V.toScheme := ⟨xO, hx⟩
  let : Nonempty (secondSource q₁ ⊤ V a₁) := ⟨(hPuncture₂ xV).choose⟩
  let : Nonempty (parameterOpen q₁ ⊤ V).toScheme := ⟨a₂ (hPuncture₂ xV).choose⟩
  let : IsIntegral (parameterOpen q₁ ⊤ V).toScheme :=
    isIntegral_of_isOpenImmersion ((parameterOpen q₁ ⊤ V).ι ≫ (parameterOpen q ⊤ O).ι)
  let : IsIntegral (secondSource q₁ ⊤ V a₁) := isIntegral_of_isOpenImmersion a₂
  let : IsAffine (parameterOpen q₁ ⊤ V).toScheme :=
    parameterOpen_affine q₁ ⊤ V (isAffineOpen_top _) hV
  let : IsAffine (firstSource q₁ ⊤ V p₁) := isAffine_of_isAffineHom p₂
  let : IsAffine (secondSource q₁ ⊤ V a₁) := isAffine_of_isAffineHom a₂
  let : IsAffine (pullback p₂ a₂) := isAffine_of_isAffineHom u₂
  let : SmoothOfRelativeDimension 1 ((a₂ ≫ jA₂) ≫ π₂) := by
    rw [Category.assoc]
    exact smoothOfRelativeDimension_comp (n := 0) (m := 1) _ _
  let : SmoothOfRelativeDimension 1 (v₂ ≫ F₂ ≫ π₂) := by
    change SmoothOfRelativeDimension 1 ((u₂ ≫ jB₂) ≫ (F₂ ≫ π₂))
    rw [Category.assoc]
    exact smoothOfRelativeDimension_comp (n := 0) (m := 1) _ _
  let : Smooth q₂ := SmoothOfRelativeDimension.smooth 1 q₂
  let : Smooth (jA₂ ≫ π₂) := SmoothOfRelativeDimension.smooth 1 _
  let : Smooth (jB₂ ≫ F₂ ≫ π₂) := SmoothOfRelativeDimension.smooth 1 _
  let : Smooth ((a₂ ≫ jA₂) ≫ π₂) := SmoothOfRelativeDimension.smooth 1 _
  let : Smooth (v₂ ≫ F₂ ≫ π₂) := SmoothOfRelativeDimension.smooth 1 _
  let : SmoothOfRelativeDimension 1 π₁ :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (isPullback_morphismRestrict π O).flip inferInstance
  let : SmoothOfRelativeDimension 1 π₂ :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (isPullback_morphismRestrict π₁ V).flip inferInstance
  let hIntegral (K : Scheme.{u}) [IsAffine K] [IsIntegral K] (b : K ⟶ V.toScheme) :
      IsIntegral (pullback b π₂) :=
    isIntegral_pullback_morphismRestrict π₁ V b
      (isIntegral_pullback_morphismRestrict π O (b ≫ V.ι)
        (isIntegral_pullback_projectiveLine ((b ≫ V.ι) ≫ O.ι)))
  let : IsIntegral (pullback (a₂ ≫ q₂) π₂) := hIntegral _ (a₂ ≫ q₂)
  let : IsFiniteLocallyFree (graphProductMap π₂ F₂ jB₂) :=
    isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
      (retainedProductInclusion_isPullback _ _ _) inferInstance
  let : IsFiniteLocallyFree (retainedProductInclusion (a₂ ≫ q₂) π₂ F₂) :=
    isFiniteLocallyFree_isStableUnderBaseChange.of_isPullback
      (retainedProductInclusion_isPullback _ _ _) inferInstance
  let : IsSeparated (terminal.from (pullback (jB₂ ≫ F₂ ≫ π₂) π₂ : Scheme.{u})) := by
    rw [show terminal.from (pullback (jB₂ ≫ F₂ ≫ π₂) π₂ : Scheme.{u}) =
      pullback.fst (jB₂ ≫ F₂ ≫ π₂) π₂ ≫
        terminal.from (firstSource q₁ ⊤ V p₁) from
        terminal.hom_ext _ _]
    infer_instance
  let t₂ := V.ι ≫ O.ι ≫ t
  let : Smooth t₂ := inferInstanceAs (Smooth (V.ι ≫ O.ι ≫ t))
  let : IsAffineHom t₂ := isAffineHom_of_isAffine t₂
  let U₂ := SmoothSite.mk t₂
  let l : U₂ ⟶ U := SmoothSite.homMk (V.ι ≫ O.ι ≫ l₀.left) (by
    change (V.ι ≫ O.ι ≫ l₀.left) ≫ U.hom = V.ι ≫ O.ι ≫ t
    have hl₀ : l₀.left ≫ U.hom = t := MorphismProperty.Over.w l₀
    simp only [Category.assoc, hl₀])
  let : IsOpenImmersion l.left := inferInstanceAs (IsOpenImmersion (V.ι ≫ O.ι ≫ l₀.left))
  let x₁ := (parameterOpen q ⊤ O).ι
  let x₂ := (parameterOpen q₁ ⊤ V).ι
  let m := x₂ ≫ x₁ ≫ m₀.left
  have hq₂ : x₂ ≫ x₁ ≫ q = q₂ ≫ V.ι ≫ O.ι := by
    calc
      _ = x₂ ≫ q₁ ≫ O.ι :=
        congrArg (fun h ↦ x₂ ≫ h) (parameterProjection_base q ⊤ O).symm
      _ = (x₂ ≫ q₁) ≫ O.ι := (Category.assoc _ _ _).symm
      _ = (q₂ ≫ V.ι) ≫ O.ι := congrArg (fun h ↦ h ≫ O.ι)
        (parameterProjection_base q₁ ⊤ V).symm
      _ = _ := Category.assoc _ _ _
  let X₂ := SmoothSite.mk ((jA₂ ≫ π₂) ≫ t₂)
  let Y₂ := SmoothSite.mk ((jB₂ ≫ F₂ ≫ π₂) ≫ t₂)
  let A₂ := SmoothSite.mk ((a₂ ≫ q₂) ≫ t₂)
  let A₂' := SmoothSite.mk (((a₂ ≫ jA₂) ≫ π₂) ≫ t₂)
  let B₂ := SmoothSite.mk ((v₂ ≫ F₂ ≫ π₂) ≫ t₂)
  let m₂ : X₂ ⟶ T := SmoothSite.homMk m (by
    change m ≫ T.hom = (jA₂ ≫ π₂) ≫ t₂
    have hm₀ : m₀.left ≫ T.hom = q ≫ t := MorphismProperty.Over.w m₀
    calc
      _ = (x₂ ≫ x₁ ≫ q) ≫ t := by
        simp only [m, Category.assoc, hm₀]
      _ = (q₂ ≫ V.ι ≫ O.ι) ≫ t := congrArg (fun h ↦ h ≫ t) hq₂
      _ = q₂ ≫ t₂ := by simp only [t₂, Category.assoc]
      _ = _ := congrArg (· ≫ t₂) (hA₂.trans (Category.id_comp q₂)).symm)
  let b₂ : X₂ ⟶ U₂ := SmoothSite.homMk q₂ (by
    change q₂ ≫ t₂ = (jA₂ ≫ π₂) ≫ t₂
    rw [hA₂, Category.id_comp])
  have Hwhole : IsPullback (m₂ ≫ eT.hom).left b₂.left ((proj).app U).left l.left := by
    change IsPullback (m ≫ eT.hom.left) q₂ ((proj).app U).left (V.ι ≫ O.ι ≫ l₀.left)
    have H₀' : IsPullback (m₀.left ≫ eT.hom.left) q ((proj).app U).left l₀.left := H₀
    simpa only [m, x₁, x₂, Category.assoc] using
      (wholeParameter_isPullback q₁ V).paste_horiz
        ((wholeParameter_isPullback q O).paste_horiz H₀')
  let E := cylinderComparisonIso l eT m₂ b₂ Hwhole
  let h := affineLineCylinder.map l ≫ eT.inv
  have he : h ≫ eT.hom = affineLineCylinder.map l := by
    simp only [h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hEm : E.hom ≫ h = m₂ := by
    calc
      _ = (E.hom ≫ affineLineCylinder.map l) ≫ eT.inv := (Category.assoc _ _ _).symm
      _ = (m₂ ≫ eT.hom) ≫ eT.inv :=
        congrArg (fun w ↦ w ≫ eT.inv) (cylinderComparisonIso_hom_map l eT m₂ b₂ Hwhole)
      _ = m₂ ≫ (eT.hom ≫ eT.inv) := Category.assoc _ _ _
      _ = m₂ := (congrArg (fun w ↦ m₂ ≫ w) eT.hom_inv_id).trans (Category.comp_id _)
  let aS : A₂ ⟶ X₂ := SmoothSite.homMk a₂ (by
    change a₂ ≫ ((jA₂ ≫ π₂) ≫ t₂) = (a₂ ≫ q₂) ≫ t₂
    rw [hA₂, Category.id_comp, Category.assoc])
  let pS : Y₂ ⟶ X₂ := SmoothSite.homMk p₂ (by
    change p₂ ≫ ((jA₂ ≫ π₂) ≫ t₂) = (jB₂ ≫ F₂ ≫ π₂) ≫ t₂
    rw [hA₂, Category.id_comp, ← Category.assoc, ← hB₂])
  let uS : B₂ ⟶ Y₂ := SmoothSite.homMk u₂ (by
    change u₂ ≫ ((jB₂ ≫ F₂ ≫ π₂) ≫ t₂) = (v₂ ≫ F₂ ≫ π₂) ≫ t₂
    simp only [v₂, Category.assoc])
  let gS : B₂ ⟶ A₂' := SmoothSite.homMk g₂ (by
    change g₂ ≫ (((a₂ ≫ jA₂) ≫ π₂) ≫ t₂) = (v₂ ≫ F₂ ≫ π₂) ≫ t₂
    calc
      _ = (g₂ ≫ (a₂ ≫ jA₂)) ≫ (π₂ ≫ t₂) := by simp only [Category.assoc]
      _ = (v₂ ≫ F₂) ≫ (π₂ ≫ t₂) := congrArg (· ≫ (π₂ ≫ t₂)) hvg.symm
      _ = _ := by simp only [Category.assoc])
  let I : A₂ ≅ A₂' := MorphismProperty.Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (((a₂ ≫ jA₂) ≫ π₂) ≫ t₂) = (a₂ ≫ q₂) ≫ t₂
    rw [Category.id_comp, Category.assoc a₂ jA₂, hA₂, Category.id_comp])
  let rAS := pullback.fst a₁ x₂ ≫ pullback.fst a x₁ ≫ rA₀
  let rYS := pullback.fst p₁ x₂ ≫ pullback.fst p x₁ ≫ rY₀
  have hAS : rAS ≫ i.left = a₂ ≫ m₂.left := by
    change rAS ≫ i.left = a₂ ≫ m
    have ha₁ : pullback.fst a x₁ ≫ a = a₁ ≫ x₁ := pullback.condition
    have ha₂ : pullback.fst a₁ x₂ ≫ a₁ = a₂ ≫ x₂ := pullback.condition
    simp only [rAS, m, Category.assoc, hA₀, reassoc_of% ha₁, reassoc_of% ha₂]
  have hYS : rYS ≫ v.left = p₂ ≫ m₂.left := by
    change rYS ≫ v.left = p₂ ≫ m
    have hp₁ : pullback.fst p x₁ ≫ p = p₁ ≫ x₁ := pullback.condition
    have hp₂ : pullback.fst p₁ x₂ ≫ p₁ = p₂ ≫ x₂ := pullback.condition
    simp only [rYS, m, Category.assoc, hY₀, reassoc_of% hp₁, reassoc_of% hp₂]
  let rAo : A₂ ⟶ Ao := SmoothSite.homMk rAS (by
    rw [← MorphismProperty.Over.w i, ← Category.assoc, hAS, Category.assoc,
      MorphismProperty.Over.w m₂]
    exact MorphismProperty.Over.w aS)
  let rYo : Y₂ ⟶ Yo := SmoothSite.homMk rYS (by
    rw [← MorphismProperty.Over.w v, ← Category.assoc, hYS, Category.assoc,
      MorphismProperty.Over.w m₂]
    exact MorphismProperty.Over.w pS)
  have hrA : rAo ≫ i = aS ≫ m₂ := MorphismProperty.Over.Hom.ext hAS
  have hrY : rYo ≫ v = pS ≫ m₂ := MorphismProperty.Over.Hom.ext hYS
  have hAB : (gS ≫ I.inv) ≫ aS = uS ≫ pS := by
    apply MorphismProperty.Over.Hom.ext
    change (g₂ ≫ 𝟙 _) ≫ a₂ = u₂ ≫ p₂
    rw [Category.comp_id]
    exact pullback.condition.symm
  let rBo := HB.lift (gS ≫ I.inv ≫ rAo) (uS ≫ rYo) (by
    simp only [Category.assoc, hrA, hrY]
    simp only [← Category.assoc, hAB])
  have hrBoA : rBo ≫ bA = gS ≫ I.inv ≫ rAo := HB.lift_fst _ _ _
  have hrBoY : rBo ≫ bY = uS ≫ rYo := HB.lift_snd _ _ _
  let eScheme := (SmoothSite.forgetScheme (Spec (.of k))).mapIso E
  let zC := z₂ ≫ eScheme.hom
  let : IsClosedImmersion z₁ := MorphismProperty.of_isPullback
    (markToParameter_isPullback q ⊤ O z (fun _ _ ↦ trivial)).flip inferInstance
  let : IsClosedImmersion z₂ := MorphismProperty.of_isPullback
    (markToParameter_isPullback q₁ ⊤ V z₁ (fun _ _ ↦ trivial)).flip inferInstance
  let : IsClosedImmersion zC := inferInstanceAs (IsClosedImmersion (z₂ ≫ eScheme.hom))
  let : IsOpenImmersion (aS ≫ E.hom).left :=
    inferInstanceAs (IsOpenImmersion (a₂ ≫ eScheme.hom))
  let : Etale (pS ≫ E.hom).left := inferInstanceAs (Etale (p₂ ≫ eScheme.hom))
  have HC : IsPullback s₂ (𝟙 _) (pS ≫ E.hom).left zC := by
    refine H₂.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) eScheme ?_ rfl ?_ ?_
    · change s₂ ≫ 𝟙 _ = 𝟙 _ ≫ s₂
      simp only [Category.comp_id, Category.id_comp]
    · change p₂ ≫ eScheme.hom = 𝟙 _ ≫ (p₂ ≫ eScheme.hom)
      exact (Category.id_comp _).symm
    · change zC = 𝟙 _ ≫ zC
      exact (Category.id_comp _).symm
  have hComp₂ : Set.range z₂ = (Set.range a₂)ᶜ := by
    ext x
    exact ⟨fun hz ha ↦ Set.disjoint_left.mp ha₂ ha hz,
      fun ha ↦ (hcover₂ x).resolve_left ha⟩
  have hCompC : Set.range zC = (Set.range (aS ≫ E.hom).left)ᶜ :=
    range_comp_iso_complement eScheme a₂ z₂ hComp₂
  have hCov : Sieve.ofTwoArrows (aS ≫ E.hom) (pS ≫ E.hom) ∈
      SmoothSite.nisnevichTopology (Spec (.of k)) (affineLineCylinder.obj U₂) := by
    apply markedCover_mem_nisnevichTopology _ _ zC s₂ HC
    · intro x
      by_cases hx : x ∈ Set.range (aS ≫ E.hom).left
      · exact Or.inl hx
      · exact Or.inr (hCompC.symm ▸ hx)
    · exact hCompC.symm ▸ disjoint_compl_right
  have hAR : rAo ≫ i = (aS ≫ E.hom) ≫ h :=
    (hrA.trans (congrArg (fun w ↦ aS ≫ w) hEm.symm)).trans (Category.assoc _ _ _).symm
  have hYR : rYo ≫ v = (pS ≫ E.hom) ≫ h :=
    (hrY.trans (congrArg (fun w ↦ pS ≫ w) hEm.symm)).trans (Category.assoc _ _ _).symm
  refine ⟨U₂, l ≫ jU, ?_⟩
  exact lift t₂ q₂ π₂ F₂ jB₂ jA₂ p₂
    hRet₂ hB₂ hA₂ a₂ z₂ s₂ hs₂ H₂ e dB₂ hdB₂ dA₂ hdA₂ ha₂ c₁ c₂
    v₂ u₂ rfl g₂ hvg hcoverB hcoverA bI₂ hbI₂ bE₂ hbE₂ hResidual Pst hPst hSrc hPunctureA
    (dA₂ ≫ π₂).surjective hIntegral jU l ⟨xV⟩ eT h he E i v bA bY rAo rYo rBo
    hAR hYR hrBoA hrBoY hCov
    σ sA sY hm hsA hsY

end AlgebraicGeometry.PresheafWithTransfers
