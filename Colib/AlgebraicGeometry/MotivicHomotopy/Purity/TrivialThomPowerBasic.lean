/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffineCylinderPowerSupport
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.RelativeLineThom
import Colib.AlgebraicGeometry.Correspondences.Coproducts.Zero

/-! # The supported Thom motive of a trivial affine bundle -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]

/-- The canonical abelian structure on sheaves with transfers. -/
local instance instAbelianTrivialThomPowerBasic : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

local instance instNoetherianTrivialThomPowerBasic :
    IsNoetherian (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) :=
  inferInstanceAs (IsNoetherian (Spec (CommRingCat.of k)))

/-- An empty open complement gives the original ambient motive as the pair quotient. -/
theorem isIso_effectivePairMotiveQuotient_of_isEmpty
    {U X : Sm} (j : U ⟶ X) [IsEmpty U.left] :
    IsIso (effectivePairMotiveQuotient k j) := by
  let F := transferRepresentable k
  let Y := Cor.mk U
  have hY : IsZero Y := (IsZero.iff_id_eq_zero _).2
    (Cor.hom_eq_zero_of_isEmpty_source k (𝟙 Y))
  have h : IsZero (F.obj Y) := F.map_isZero hY
  let f := (smoothTransferRepresentable k).map j
  have hf : f = 0 := h.eq_of_src _ _
  let : IsIso ((transferPairProjection k).app (Arrow.mk j)) :=
    cokernel.π_of_zero hf
  unfold effectivePairMotiveQuotient
  infer_instance

variable [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]

local notation "M" => effectiveSmoothMotive k
local notation "L" => effectiveLefschetzTwistFunctor k
local notation "T(" n ")" => Stabilization.iterate L n

set_option maxHeartbeats 750000 in
-- Keep the degree-zero quotient and the successor comparison at the literal tower objects.
/-- The Thom isomorphism for the literal trivial bundle of any finite rank.
Its successor is the original nested-open boundary followed by the reduced
Laurent projection. -/
def effectiveTrivialPowerThomIso (X : Sm) (n : ℕ) :
    effectiveMotiveWithSupport k (affineCylinderPowerZero k X n) ≅
      (T(n)).obj ((M).obj X) := by
  induction n with
  | zero =>
      let W := affineCylinderPower k X 0
      let z := affineCylinderPowerZero k X 0
      let U := (opensFunctor W).obj (closedPairOpen z.left)
      let u : U ⟶ W := closedPairOpenInclusion z.left
      letI : IsEmpty U.left := by
        constructor
        intro x
        exact x.property ⟨x.val, rfl⟩
      have h : IsIso (effectivePairMotiveQuotient k u) :=
        isIso_effectivePairMotiveQuotient_of_isEmpty k (U := U) (X := W) u
      exact (@asIso _ _ _ _ (effectivePairMotiveQuotient k u) h).symm
  | succ n e =>
      exact effectiveAppendZeroSectionThomIso k (affineCylinderPowerZero k X n) ≪≫ (L).mapIso e

/-- The isomorphism is the Thom map of the specified tower of native lines,
transported by the coordinate comparison that carries the actual zero section. -/
def effectiveAffineSpaceThomIso (X : Sm) [IsAffine X.left] (n : ℕ) :
    effectiveMotiveWithSupport k (relativeAffineSpaceZeroSection X n) ≅ (T(n)).obj ((M).obj X) :=
  ((effectivePairMotiveFunctor k).mapIso (affineCylinderPowerSupportIso k X n)).symm ≪≫
    effectiveTrivialPowerThomIso k X n

/-- The normalized supported class uses the original structure map of the base. -/
def effectiveAffineSpaceThomClass (X : Sm) [IsAffine X.left] (n : ℕ) :
    effectiveMotiveWithSupport k (relativeAffineSpaceZeroSection X n) ⟶
      (T(n)).obj ((M).obj (base S)) :=
  (effectiveAffineSpaceThomIso k X n).hom ≫ (T(n)).map ((M).map (toBase X))

end AlgebraicGeometry.MotivicHomotopy
