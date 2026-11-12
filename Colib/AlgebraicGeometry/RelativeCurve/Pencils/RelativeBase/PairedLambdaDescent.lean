/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedLambdaDescentCore
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedNormUnit

/-!
# The global difference of the two original lambda actions

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
  (π : P ⟶ S) [IsProper π] [SmoothOfRelativeDimension 1 π] (f : C ⟶ P) [IsFinite f]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ f ≫ π)]
  (jA : X ⟶ P) [IsOpenImmersion jA] [SmoothOfRelativeDimension 1 (jA ≫ π)]
  (p : Y ⟶ X) [Flat p] (hRet : j ≫ f = p ≫ jA)
  (hB : j ≫ (f ≫ π) = p ≫ q) (hA : jA ≫ π = (𝟙 X) ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a] [SmoothOfRelativeDimension 1 ((a ≫ jA) ≫ π)]
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
    SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)
  (d₁ : D₁ ⟶ C) (hd₁ : Disjoint (Set.range j) (Set.range d₁))
  (d₂ : D₂ ⟶ P) [IsClosedImmersion d₂] [IsClosedImmersion (z ≫ jA)]
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

local instance pairedLambdaDescentSourceSmooth : Smooth b := SmoothOfRelativeDimension.smooth 1 b
local instance pairedLambdaDescentTargetSmooth : Smooth bA := SmoothOfRelativeDimension.smooth 1 bA
local instance pairedLambdaDescentOverlapSmooth : Smooth rB := SmoothOfRelativeDimension.smooth 1 rB
local instance pairedLambdaDescentPunctureSmooth : Smooth rA :=
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

variable [hFinite : IsFiniteLocallyFree (graphProductMap π f j)]
  [hSeparated : IsSeparated (terminal.from (pullback (j ≫ f ≫ π) π : Scheme.{u}))]
  (bI : pullback f d₂ ⟶ D₁) (hbI : bI ≫ d₁ = pullback.fst f d₂)

set_option maxHeartbeats 1000000 in
-- The open cover retains the actual unit and correspondence on each component.
include hRet hg hc₁ hc₂ hbI in
/-- The same two lambda spans have equal transfer after their two original
maps to the puncture. This equality uses the actual finite compactification
and the unit on the full boundary, and holds on the Nisnevich unit image. -/
theorem nisnevichImage_transfer_pairedLambdaDifference_zero
    (Pst : PresheafWithTransfers.{u + 1} k) (hPst : Pst.IsA1Invariant)
    (hSrc : SourceMarkedBoundaryGeneration π f j zA s d₁)
    (hResidual : ∀ (T : Scheme.{u}) (w : T ⟶ pullback (j ≫ f ≫ π) π),
      PairedNormChartResidualFactor π f j jA p hRet z s H w d₁)
    (hPuncture : Function.Surjective rA) (hInfinity : Function.Surjective (d₂ ≫ π))
    (hIntegral : ∀ (K : Scheme.{u}) [IsAffine K] [IsIntegral K] (bK : K ⟶ S),
      IsIntegral (pullback bK π)) :
    (nisnevichImage Pst).transfer
      (c₁.lambda t v hc₁ ≫ (Cor.graphFunctor k).map g₀ -
        (Cor.graphFunctor k).map p₀ ≫ c₂.lambda t (a ≫ jA) hc₂) = 0 := by
  have hUnit : HasPairedNormUnit q π f j jA p hRet hB hA
      a z s hs H e d₁ hd₁ d₂ hd₂ ha c₁ c₂ :=
    exists_pairedNormUnit q π f j jA p hRet hB hA a z s hs H e d₁ hd₁ d₂ hd₂ ha
      c₁ c₂ bI (hFinite := hFinite) (hSep := hSeparated) hSrc hbI hResidual
  exact nisnevichImage_transfer_pairedLambdaDifference_zero_of_pairedNormUnit
    t q π f j jA p hRet hB hA a z s hs H e d₁ hd₁ d₂ hd₂ ha c₁ c₂
    v g hg hc₁ hc₂ Pst hPst hPuncture hInfinity hIntegral hUnit

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
