/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.SmoothProduct
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffineSpaceThom
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ThomGraphBasic
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # The supported Thom graph of the original affine-space origin -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true

open CategoryTheory MonoidalCategory AlgebraicGeometry.Scheme
open SmoothSite Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

private theorem isIso_affineGraph_comp {C : Type*} [Category* C] (F : C ⥤ C)
    {A A₀ Q Q₀ K : C} (a : A ⟶ Q) (d : Q ⟶ Q₀) (g : A ⟶ A₀)
    (e : F.obj A ≅ Q) (e₀ : F.obj A₀ ≅ Q₀) (t : A ⟶ K) (t₀ : A₀ ⟶ K)
    (h : CommSq (F.map g) e.hom e₀.hom d) (ht : t = g ≫ t₀)
    [IsIso (a ≫ d)] [IsIso t₀] :
    IsIso (a ≫ e.inv ≫ F.map t) := by
  rw [ht, F.map_comp, ← h.vert_inv.w_assoc (F.map t₀), ← Category.assoc a d]
  infer_instance

variable (k : Type u) [Field k] [PerfectField k]

attribute [local instance] thomGraphBasicCorSheafify thomGraphBasicSmoothSheafify

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S
local notation "E" => EffectiveMotivesMinus k
local notation "B" => base S
local notation "M" => effectiveSmoothMotive k
local notation "Φ" => effectivePairMotiveFunctor k
attribute [local instance] thomGraphBasicAbelian thomGraphBasicMonoidal

attribute [local irreducible] effectivePairThomGraph
attribute [local irreducible] Cor.graphFunctor SheafWithTransfers.transferRepresentable
attribute [local irreducible] SmoothSite.opensFunctor relativeAffineSpace

set_option maxHeartbeats 900000 in
-- The product comparison is on the original smooth pair functors.
/-- The supported graph applied to the actual normalized class is invertible on a trivial chart. -/
theorem isIso_effectiveAffineSpaceThomGraph (Y : Sm) [IsAffine Y.left] (n : ℕ) :
    IsIso (effectivePairThomGraph k
      (j := closedPairOpenInclusion (relativeAffineSpaceZeroSection Y n).left)
      (affineSpaceProjection Y n)
      (effectiveAffineSpaceThomClass k Y n)) := by
  let j := closedPairOpenInclusion (relativeAffineSpaceZeroSection Y n).left
  let j₀ := closedPairOpenInclusion (relativeAffineSpaceZeroSection B n).left
  let f : Arrow.mk j ⟶ Arrow.mk j₀ :=
    closedSupportArrowMap
      (i := relativeAffineSpaceZeroSection Y n) (j := relativeAffineSpaceZeroSection B n)
      (f := affineSpaceObjectMap (toBase Y) n) (g := toBase Y)
      (affineSpaceOrigin_isPullback (toBase Y) n)
  let a := pairProductGraph j (affineSpaceProjection Y n)
  let d := (parameterProduct Y).mapArrow.map f
  let g : effectivePairMotive k j ⟶ effectivePairMotive k j₀ := (Φ).map f
  let e := effectivePairProductRightIso k j Y
  let e₀ := effectivePairProductRightIso k j₀ Y
  let F : E ⥤ E := tensorRight ((M).obj Y)
  let : IsAffine (base S).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))
  let t₀ := (effectiveAffineSpaceThomIso k B n).hom
  have ht : effectiveAffineSpaceThomClass k Y n = g ≫ t₀ :=
    (effectiveAffineSpaceThomIso_naturality k (toBase Y) n).symm
  have hs : CommSq (F.map g) e.hom e₀.hom ((Φ).map d) :=
    ⟨effectivePairProductRightIso_naturality k f Y⟩
  let : IsIso (a ≫ d) := by
    rw [affineSpacePairProductGraph_eq Y n]
    infer_instance
  let : IsIso ((Φ).map a ≫ (Φ).map d) := by
    rw [← (Φ).map_comp]
    infer_instance
  unfold effectivePairThomGraph
  exact isIso_affineGraph_comp F ((Φ).map a) ((Φ).map d) g e e₀
    (effectiveAffineSpaceThomClass k Y n) t₀ hs ht

end AlgebraicGeometry.MotivicHomotopy
