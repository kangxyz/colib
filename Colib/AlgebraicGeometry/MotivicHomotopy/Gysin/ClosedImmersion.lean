/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.DeformationComparison
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.SupportedTateComparison
public import Colib.CategoryTheory.Triangulated.ThirdObjectIso
import Colib.Util.References
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # Motivic purity and the Gysin triangle of a smooth closed pair -/

@[expose] public noncomputable section

open AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Pretriangulated
open SmoothSite

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]

/-- The canonical additive sheafification on the Nisnevich correspondence site. -/
local instance gysinCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

/-- The canonical additive sheafification on the smooth Nisnevich site. -/
local instance gysinSmoothSheafify :
    HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "E" => EffectiveMotivesMinus k
local notation "M" => effectiveSmoothMotive k

/-- The canonical abelian structure on sheaves with transfers. -/
local instance gysinAbelian : Abelian (SheafWithTransfers.{u + 1} k) := SheafWithTransfers.abelian k
local notation "L" => effectiveLefschetzTwistFunctor k

set_option Elab.async false in
set_option maxHeartbeats 900000 in
-- Match the relative normal fibre with the chosen Thom isomorphism.
/-- Motivic purity for a smooth closed pair of the indicated pure dimensions. -/
@[colib_tag "COL-1225", colib_ref "Deglise2012GysinI" "Theorem 2.14 and formula (2.14.a)"
  "adaptation" "Purity in the original bounded-above effective category"]
def effectivePurity
    {Z X : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ X)
    [IsClosedImmersion i.left] {n m : ℕ}
    (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m) :
    effectiveMotiveWithSupport k i ≅ (Stabilization.iterate L (n - m)).obj ((M).obj Z) :=
  effectivePurityOfThom k i hX hZ (effectiveNormalBundleThomIso k i hX hZ)

set_option Elab.async false in
set_option maxHeartbeats 800000 in
-- Use the original quotient and the specified Lefschetz endpoint.
/-- The closed-immersion Gysin morphism is the complementary-open quotient followed by purity. -/
@[colib_tag "COL-1226"]
def effectiveGysin
    {Z X : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ X)
    [IsClosedImmersion i.left] {n m : ℕ}
    (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m) :
    (M).obj X ⟶ (Stabilization.iterate L (n - m)).obj ((M).obj Z) :=
  effectivePairMotiveQuotient k (closedPairOpenInclusion i.left) ≫
    (effectivePurity k i hX hZ).hom

set_option Elab.async false in
set_option maxHeartbeats 800000 in
-- Use the actual third object of the relative triangle.
/-- The Gysin triangle with the actual open immersion, quotient and boundary. -/
@[colib_tag "COL-1226"]
def effectiveGysinTriangle
    {Z X : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ X)
    [IsClosedImmersion i.left] {n m : ℕ}
    (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m) : Triangle E :=
  (effectivePairTriangle k (closedPairOpenInclusion i.left)).ofIso₃
    (effectivePurity k i hX hZ)

set_option Elab.async false in
set_option maxHeartbeats 1000000 in
-- Use the original relative triangle at the indicated purity isomorphism.
/-- The Gysin triangle is distinguished for the given smooth closed pair. -/
@[colib_tag "COL-1226", colib_ref "Voevodsky2000TriangulatedMotives" "Proposition 3.5.4"
  "adaptation" "The distinguished Gysin triangle with the original pair boundary",
  colib_ref "Deglise2012GysinI" "Definition 2.20" "specialization"
    "The Gysin quotient and residue defined by transport along purity"]
theorem effectiveGysinTriangle_distinguished
    {Z X : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ X)
    [IsClosedImmersion i.left] {n m : ℕ}
    (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m) :
    effectiveGysinTriangle k i hX hZ ∈ distTriang E := by
  let j := closedPairOpenInclusion i.left
  exact (effectivePairTriangle k j).ofIso₃_distinguished (effectivePurity k i hX hZ)
    (effectivePairTriangle_distinguished k j)

attribute [colib_tag "COL-1305",
  colib_ref "MorelVoevodsky1999" "Section 3.2, Proposition 2.24, page 115" "adaptation"
    "Both deformation fibre maps on integral relative effective motives"]
  effectiveDeformationComparison

attribute [colib_tag "COL-1305"]
  isIso_effectivePairMotiveMap_deformationOne
  isIso_effectivePairMotiveMap_deformationZero
  effectiveDeformationComparison_hom_comp_normal

attribute [colib_tag "COL-1298",
  colib_ref "Deglise2012GysinI" "Theorem 2.14(2) and formula (2.14.a)" "adaptation"
    "The normal-bundle step with the normalized local Thom classes",
  colib_ref "Deglise2012GysinI" "Example 2.21 and formula (2.21.b)" "adaptation"
    "The bundle projection graph followed by tensoring with the Thom class"]
  effectiveNormalBundleThomIso

attribute [colib_tag "COL-1298"]
  normalBundleThomClass isIso_effectiveNormalBundleThomGraph

end AlgebraicGeometry.MotivicHomotopy
