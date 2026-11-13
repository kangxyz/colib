/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.ActionDetection
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.ParameterBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedLambdaAction
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedNormUnitData
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.GermInjective

/-!
# Descending the paired lambda action along an affine cover

The same norm unit is pulled back to integral affine neighborhoods of the
actual source. The entire boundary and the two original correspondences
restrict together, and Nisnevich separatedness gives the global action.

Adapted from `NativeSectionPairGlobalDifferenceZero.lean` under
`Motivic/Transfers/Presheaf/Actions/Pencils` at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.Divisors Stacks.Morphisms

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

open PresheafWithTransfers

variable {k : Type u} [Field k] {S X Y P C A Z D₁ D₂ V : Scheme.{u}}
  [IsAffine S] [IsAffine X] [IsAffine Y] [IsAffine A] [IsAffine V]
  (t : S ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ S) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (π : P ⟶ S) [IsProper π] (f : C ⟶ P) [IsFinite f]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ f ≫ π)]
  (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (p : Y ⟶ X) [Flat p] (hRet : j ≫ f = p ≫ jA)
  (hB : j ≫ (f ≫ π) = p ≫ q) (hA : jA ≫ π = (𝟙 X) ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a] [SmoothOfRelativeDimension 1 ((a ≫ jA) ≫ π)]
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
  (d₁ : D₁ ⟶ C) (hd₁ : Disjoint (Set.range j) (Set.range d₁))
  (d₂ : D₂ ⟶ P)
  (hd₂ : Disjoint (Set.range jA) (Set.range d₂))
  (ha : Disjoint (Set.range a) (Set.range z))
  (c₁ : SectionData q (f ≫ π) j p hB a z s hs H e d₁ hd₁ ha)
  (c₂ : SectionData q π jA (𝟙 X) hA a z z (Category.comp_id z) (IsPullback.of_id_snd)
    e d₂ hd₂ ha)
  (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ f ≫ π)]
  (g : V ⟶ A) (hg : v ≫ f = g ≫ (a ≫ jA))
  (hc₁ : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range d₁ ∨ x ∈ Set.range (s ≫ j))
  (hc₂ : ∀ x : P, x ∈ Set.range (a ≫ jA) ∨ x ∈ Set.range d₂ ∨
    x ∈ Set.range (z ≫ jA))

local notation "b" => (j ≫ f ≫ π)
local notation "bA" => (jA ≫ π)
local notation "rB" => (v ≫ f ≫ π)
local notation "rA" => ((a ≫ jA) ≫ π)
local notation "zA" => (z ≫ jA)

local instance smoothPairedDescentSource : Smooth b := SmoothOfRelativeDimension.smooth 1 b
local instance smoothPairedDescentParameter : Smooth bA := SmoothOfRelativeDimension.smooth 1 bA
local instance smoothPairedDescentRetainedSource : Smooth rB :=
  SmoothOfRelativeDimension.smooth 1 rB
local instance smoothPairedDescentRetainedTarget : Smooth rA :=
  SmoothOfRelativeDimension.smooth 1 rA

local notation "Y₀" => (SmoothSite.mk (b ≫ t))
local notation "X₀" => (SmoothSite.mk (bA ≫ t))
local notation "V₀" => (SmoothSite.mk (rB ≫ t))
local notation "A₀" => (SmoothSite.mk (rA ≫ t))

local notation "hSourceBase" => (show p ≫ bA = b from by
  rw [← Category.assoc p jA π, ← hRet, Category.assoc])
local notation "hTargetBase" => (show g ≫ rA = rB from by
  rw [← Category.assoc g (a ≫ jA) π, ← hg, Category.assoc])
local notation "p₀" => (SmoothSite.homMk (X := Y₀) (Y := X₀) p
  ((Category.assoc p bA t).symm.trans (congrArg (fun w ↦ w ≫ t) hSourceBase)))
local notation "g₀" => (SmoothSite.homMk (X := V₀) (Y := A₀) g
  ((Category.assoc g rA t).symm.trans (congrArg (fun w ↦ w ≫ t) hTargetBase)))

variable [IsFiniteLocallyFree (graphProductMap π f j)]

set_option maxHeartbeats 800000 in
-- The open cover retains the actual unit and correspondence on each component.
include hRet hg hc₁ hc₂ in
/-- The same two lambda spans have equal transfer after their two original
maps to the puncture. This equality uses the actual finite compactification
and the unit on the full boundary, and holds on the Nisnevich unit image. -/
theorem nisnevichImage_transfer_pairedLambdaDifference_zero_of_pairedNormUnit
    (Pst : PresheafWithTransfers.{u + 1} k) (hPst : Pst.IsA1Invariant)
    (hPuncture : Function.Surjective rA) (hInfinity : Function.Surjective (d₂ ≫ π))
    (hIntegral : ∀ (K : Scheme.{u}) [IsAffine K] [IsIntegral K] (bK : K ⟶ S),
      IsIntegral (pullback bK π)) :
    HasPairedNormUnit q π f j jA p hRet hB hA a z s hs H e d₁ hd₁ d₂ hd₂ ha c₁ c₂ →
    (nisnevichImage Pst).transfer
      (c₁.lambda t v hc₁ ≫ (Cor.graphFunctor k).map g₀ -
        (Cor.graphFunctor k).map p₀ ≫ c₂.lambda t (a ≫ jA) hc₂) = 0 := by
  intro hUnit
  let : IsNoetherian Y := inferInstanceAs (IsNoetherian (Y₀).left)
  let : IsNoetherian X := inferInstanceAs (IsNoetherian (X₀).left)
  let : IsNoetherian (pullback b (f ≫ π)) :=
    isNoetherian_of_finiteType_of_isNoetherian (pullback.fst b (f ≫ π))
  let : IsNoetherian (pullback bA π) :=
    isNoetherian_of_finiteType_of_isNoetherian (pullback.fst bA π)
  let : IsNormal (Spec (.of k)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed k)
  let : IsNormal Y := AlgebraicGeometry.isNormal_of_smooth (b ≫ t)
  obtain ⟨U, _hFiniteLocallyFree, ha₁, ha₂, r, l, hr, hl, hunit, hnorm⟩ := hUnit
  have hcover := wholeBoundary_cover_of_secondFactor b π (a ≫ jA) d₂ zA U l hl hc₂
  have hsurj := wholeBoundary_surjective_firstProjection b π d₂ zA U l hl hInfinity
  have hNeighborhood (y : Y) : ∃ W : Y.Opens, y ∈ W ∧ IsAffineOpen W ∧
      IsIntegral W.toScheme := by
    obtain ⟨W, hy, hAff, hGerm⟩ := exists_affineOpen_germ_injective_of_isLocallyNoetherian Y y
    let : IsDomain Γ(Y, W) := Function.Injective.isDomain (Y.presheaf.germ W y hy).hom hGerm
    exact ⟨W, hy, hAff, IsIntegral.of_isIso hAff.isoSpec.inv⟩
  choose K hmem hAff hInt using hNeighborhood
  let bK (y : Y) := (K y).ι ≫ b
  let Ksite (y : Y) := SmoothSite.mk (bK y ≫ t)
  let α (y : Y) : Ksite y ⟶ Y₀ := SmoothSite.homMk (K y).ι (Category.assoc _ _ _).symm
  let (y : Y) : IsOpenImmersion (α y).left := inferInstanceAs (IsOpenImmersion (K y).ι)
  let δ : Cor.mk Y₀ ⟶ Cor.mk A₀ := c₁.lambda t v hc₁ ≫ (Cor.graphFunctor k).map g₀ -
    (Cor.graphFunctor k).map p₀ ≫ c₂.lambda t (a ≫ jA) hc₂
  change (nisnevichImage Pst).transfer δ = 0
  refine nisnevichImage_transfer_eq_zero_of_open_cover Pst Ksite α
    (fun y ↦ ⟨y, ⟨y, hmem y⟩, rfl⟩) δ ?_
  intro y
  let : IsAffine (K y).toScheme := hAff y
  let : IsIntegral (K y).toScheme := hInt y
  let : IsNoetherian (K y).toScheme := inferInstanceAs (IsNoetherian (Ksite y).left)
  let ρ := retainedSourceChange b (bK y) π (K y).ι rfl
  let : IsIntegral (pullback (bK y) π) := hIntegral (K y).toScheme (bK y)
  let : IsNoetherian (pullback (bK y) π) :=
    isNoetherian_of_finiteType_of_isNoetherian (pullback.fst (bK y) π)
  let : IsNoetherian (pullback (bK y) (f ≫ π)) :=
    isNoetherian_of_finiteType_of_isNoetherian (pullback.fst (bK y) (f ≫ π))
  let : Nonempty (retainedProduct (bK y) π (a ≫ jA)) := by
    let x : (K y).toScheme := ⟨y, hmem y⟩
    obtain ⟨w, hw⟩ := hPuncture (bK y x)
    obtain ⟨z, -, -⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_hasPullback (bK y) rA) x w hw.symm
    exact ⟨z⟩
  let : Nonempty (pullback (K y).ι (l ≫ U.ι ≫ pullback.fst b π) : Scheme.{u}) :=
    nonempty_boundary_parameterChange b (K y).ι π U l hsurj
  obtain ⟨l', hcover', hunit'⟩ := exists_boundary_parameterChange
    b (bK y) (K y).ι rfl π (a ≫ jA) U l r hcover hunit
  let : Nonempty (ρ ⁻¹ᵁ U) := ⟨l' (Classical.choice inferInstance)⟩
  have hlocal := transfer_componentLambdaDifference_eq_zero t q π f j jA p hRet hB hA
    a z s hs H e d₁ hd₁ d₂ hd₂ ha c₁ c₂ (K y).ι v g hg hc₁ hc₂ U
    (nisnevichImage Pst) (nisnevichImage_isA1Invariant Pst hPst) r hr l' hcover' hunit'
    ha₁ ha₂ hnorm
  have hcomp : α y ≫ p₀ = (show Ksite y ⟶ X₀ from SmoothSite.homMk ((K y).ι ≫ p) (by
      change ((K y).ι ≫ p) ≫ (bA ≫ t) = ((K y).ι ≫ b) ≫ t
      rw [← Category.assoc ((K y).ι ≫ p) bA t, Category.assoc (K y).ι p bA,
        hSourceBase])) := MorphismProperty.Over.Hom.ext rfl
  simpa only [δ, Preadditive.comp_sub, ← Category.assoc, ← Functor.map_comp, hcomp]
    using hlocal

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
