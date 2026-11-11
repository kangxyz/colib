/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedSignedSourceEndpoints
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RestrictionDifference.Basic

/-!
# Restriction differences from the actual two-source retained tensor pencil

The genuine geometric family, original four whole supports, actual source maps
and section-preserving zero-ideal comparisons produce the literal restriction
relation for every original coefficient section. Only ordinary coefficient A1
invariance is used. Both endpoint equations are derived, not supplied.

This is a lower geometric-to-coefficient bridge. It does not assert existence
of the two marked correction neighborhoods or the boundary epimorphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

open Cor Scheme Scheme.PolynomialSectionPencil Scheme.RelativeCurvePencil
open Scheme.SmoothSite.Contraction

variable {k : Type u} [Field k] {S X T V Y : Scheme.{u}}
  (t : S ⟶ Spec (.of k)) [IsSeparated t]
  (q : X ⟶ S) (qA : T ⟶ S) (qN : V ⟶ S) (r : Y ⟶ S)
  [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)]
  [Smooth (qA ≫ t)] [IsSeparated (qA ≫ t)] [QuasiCompact (qA ≫ t)]
  [Smooth (qN ≫ t)] [IsSeparated (qN ≫ t)] [QuasiCompact (qN ≫ t)]
  [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)]
  [IsSeparated r] [SmoothOfRelativeDimension 1 r]
  (α : X ⟶ T) (hα : α ≫ qA = q) [Flat α]
  (β : X ⟶ V) (hβ : β ≫ qN = q) [Flat β]
  (φ : X ⟶ Y) (hφ : φ ≫ r = q)
  (M N : (pullback q r).Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property M]
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property N]

local notation "U" => SmoothSite.mk (q ≫ t)
local notation "UA" => SmoothSite.mk (qA ≫ t)
local notation "UN" => SmoothSite.mk (qN ≫ t)
local notation "W" => SmoothSite.mk (r ≫ t)
local notation "C" => pullback q r
local notation "G" => relativeGraphIdeal q r φ hφ
local notation "F" => divisorSheaf G
local notation "L" => tensorModules (tensorModules F M) N
local notation "LP" => tensorModules M N
local notation "jA" => retainedSourceChange qA q r α hα
local notation "jN" => retainedSourceChange qN q r β hβ
local notation "αs" => (show U ⟶ UA from
  SmoothSite.homMk α (by simp only [← Category.assoc, hα]))
local notation "βs" => (show U ⟶ UN from
  SmoothSite.homMk β (by simp only [← Category.assoc, hβ]))
local notation "φs" => (show U ⟶ W from
  SmoothSite.homMk φ (by simp only [← Category.assoc, hφ]))

variable (a : Γ(tensorModules F M, ⊤)) (b : Γ(M, ⊤)) (n d : Γ(N, ⊤))
  (IA IB : (pullback qA r).IdealSheafData) (IN ID : (pullback qN r).IdealSheafData)
  [IsFinite (IA.subschemeι ≫ pullback.fst qA r)]
  [Flat (IA.subschemeι ≫ pullback.fst qA r)]
  [IsFinite (IB.subschemeι ≫ pullback.fst qA r)]
  [Flat (IB.subschemeι ≫ pullback.fst qA r)]
  [IsFinite (IN.subschemeι ≫ pullback.fst qN r)]
  [Flat (IN.subschemeι ≫ pullback.fst qN r)]
  [IsFinite (ID.subschemeι ≫ pullback.fst qN r)]
  [Flat (ID.subschemeι ≫ pullback.fst qN r)]
  (ha : zeroScheme C (tensorModules F M) a = IA.comap jA)
  (hb : zeroScheme C M b = IB.comap jA)
  (hn : zeroScheme C N n = IN.comap jN)
  (hd : zeroScheme C N d = ID.comap jN)

local notation "s₀" => tensorSection (tensorModules F M) N ⊤
  (tensorSection F M ⊤ (divisorSheafGlobalSection G) b) d
local notation "s₁" => tensorSection (tensorModules F M) N ⊤ a n
local notation "pole" => tensorSection M N ⊤ b d
local notation "P" => zeroScheme C LP pole
local notation "familySourceNative" => familySource (q ≫ t) (pullback.fst q r) L s₀ s₁ ≫
  (nativeParameterIso (.of k) U).inv
local notation "δ" => retainedPencilDifference t q r L LP s₀ s₁ pole
local notation "lam" =>
  ofFiniteFlatSpan (X := UA) (Y := W)
    (IA.subschemeι ≫ pullback.fst qA r) (IA.subschemeι ≫ pullback.snd qA r)
    (by simp only [Category.assoc, pullback.condition_assoc]) -
  ofFiniteFlatSpan (X := UA) (Y := W)
    (IB.subschemeι ≫ pullback.fst qA r) (IB.subschemeι ≫ pullback.snd qA r)
    (by simp only [Category.assoc, pullback.condition_assoc])
local notation "psi" =>
  ofFiniteFlatSpan (X := UN) (Y := W)
    (ID.subschemeι ≫ pullback.fst qN r) (ID.subschemeι ≫ pullback.snd qN r)
    (by simp only [Category.assoc, pullback.condition_assoc]) -
  ofFiniteFlatSpan (X := UN) (Y := W)
    (IN.subschemeι ≫ pullback.fst qN r) (IN.subschemeι ≫ pullback.snd qN r)
    (by simp only [Category.assoc, pullback.condition_assoc])

variable [hfamilyFinite : IsFinite familySourceNative] [hfamilyFlat : Flat familySourceNative]
  [hpoleFinite : IsFinite (P.subschemeι ≫ pullback.fst q r)]
  [hpoleFlat : Flat (P.subschemeι ≫ pullback.fst q r)]

include ha hb hn hd hfamilyFinite hfamilyFlat hpoleFinite hpoleFlat in
/-- The actual retained tensor family produces the original signed lifting
relation. The first transfer is numerator-minus-pole, and the second is
pole-minus-numerator; the coefficient lifts have the two negative signs. -/
theorem hasRestrictionDifferenceLifting_of_retained_tensor_pencil
    (Pcoeff : PresheafWithTransfers.{u + 1} k) (hP : Pcoeff.IsA1Invariant)
    (hbc : IsEffectiveCartierDivisor (zeroScheme C M b))
    (hnc : IsEffectiveCartierDivisor (zeroScheme C N n))
    (hdc : IsEffectiveCartierDivisor (zeroScheme C N d)) :
    HasRestrictionDifferenceLifting Pcoeff φs βs αs := by
  obtain ⟨h₀, h₁⟩ := retainedTensorDifference_source_endpoints t q qA qN r
    α hα β hβ φ hφ M N a b n d IA IB IN ID ha hb hn hd hbc hnc hdc
  exact hasRestrictionDifferenceLifting_of_homotopy Pcoeff hP φs βs αs lam psi δ h₀ h₁

end AlgebraicGeometry.PresheafWithTransfers
