/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.RelativeLineProjection
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.RelativeLineExcision

/-! # The first arrow of the original nested relative line triangle -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite SmoothSite.Contraction

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

attribute [local irreducible] Cor.graphFunctor transferRepresentable

private def transportMapIso {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (h : F = G) {X Y : C} (f : X ⟶ Y)
    (e : { e : F.obj X ≅ F.obj Y // e.hom = F.map f }) :
    { e : G.obj X ≅ G.obj Y // e.hom = G.map f } :=
  h ▸ e

private theorem map_nested_projection {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A₀ A₁ A₂ A₃ A₄ : C}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₄) (p : A₀ ⟶ A₄)
    (e : F.obj A₀ ≅ F.obj A₁) (v : F.obj A₂ ⟶ F.obj A₄)
    (h : a ≫ b ≫ c ≫ d = p) (he : e.hom = F.map a)
    (hv : v = F.map c ≫ F.map d) : F.map b ≫ v = e.inv ≫ F.map p := by
  apply e.eq_inv_comp.2
  rw [he, hv, ← F.map_comp c d, ← F.map_comp b _, ← F.map_comp a _, h]

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S
variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "P" => effectivePairMotiveFunctor k

/-- The canonical abelian structure on sheaves with transfers. -/
local instance instAbelianRelativeLineNestedProjection : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

private abbrev relativeLineRawPairFunctor : Arrow Sm ⥤ EffectiveMotivesMinus k :=
  ((smoothTransferRepresentable k).mapArrow ⋙ coker (LargeSheaves k)) ⋙ effectiveTransferSheaf k

set_option maxHeartbeats 650000 in
-- Identify the two literal presentations before applying them to any pair.
private theorem relativeLineRawPairFunctor_eq :
    relativeLineRawPairFunctor k = P := by
  unfold effectivePairMotiveFunctor transferPairCokernelFunctor
  rfl

set_option maxHeartbeats 650000 in
-- The square notation and arrow-functor notation use the same original quotient map.
private theorem relativeLinePairMotiveMap_eq (s : Square Sm) :
    effectivePairMotiveMap k s = (P).map (Arrow.homMk' s.f₁₂ s.f₃₄ s.fac) := by
  unfold effectivePairMotiveMap effectivePairMotiveFunctor
  rfl

variable {U X W : SmoothSite (Spec (CommRingCat.of k))} (j : U ⟶ X)
  (i : affineLineCylinder.obj U ⟶ W) (l : torusCylinder.obj X ⟶ W)
  (v : W ⟶ affineLineCylinder.obj X)
  (hi : i ≫ v = affineLineCylinder.map j) (hl : l ≫ v = openInclusion.app X)

variable [IsOpenImmersion j.left] [IsOpenImmersion v.left]
  [IsOpenImmersion i.left] [IsOpenImmersion l.left]
  (hpb : (relativeLineOpenCoverSquare k j i l v hi hl).IsPullback)
  (hcover : Set.range i.left ∪ Set.range l.left = Set.univ)

local notation "T" => effectiveNestedPairTriangle k i v

set_option maxHeartbeats 1400000 in
-- Compose the checked component maps in the original quotient functor.
/-- Under the affine and Laurent comparisons, the first arrow is the original
Laurent projection. -/
theorem relativeLineNestedFirst
    (p : effectivePairMotive k (torusCylinder.map j) ⟶ effectivePairMotive k j)
    (hp : p = (P).map (relativeLaurentProjectionArrow k j)) :
    (T).mor₁ ≫ (relativeLineAffineComparison k j i v hi).hom =
      (relativeLineLaurentComparison k j i l v hi hl hpb hcover).inv ≫ p := by
  let F := P
  let a := relativeLineLaurentArrow k j i l v hi hl
  let b := relativeLineNestedArrow k i v
  let c := (relativeLineAffineArrowIso k j i v hi).hom
  let d := relativeLineAffineProjectionArrow k j
  let q := relativeLaurentProjectionArrow k j
  let ε := relativeLineLaurentComparison k j i l v hi hl hpb hcover
  let e := relativeLineAffineComparison k j i v hi
  have hε : ε.hom = F.map a := (transportMapIso (relativeLineRawPairFunctor_eq k) a
    (relativeLineLaurentComparisonData k j i l v hi hl hpb hcover)).property
  have he₀ := (relativeLineAffineComparisonData k j i v hi).property
  have he₁ := relativeLinePairMotiveMap_eq k (SmoothSite.affinePairProjectionSquare j)
  have he : e.hom = F.map c ≫ F.map d := he₀.trans (congrArg (F.map c ≫ ·) he₁)
  have ht : (T).mor₁ = F.map b := (effectiveNestedPairTriangle_mor₁ k i v).trans
    (relativeLinePairMotiveMap_eq k (nestedPairFirstSquare k i v))
  have hc := map_nested_projection F
    (A₀ := Arrow.mk (torusCylinder.map j)) (A₁ := Arrow.mk i) (A₂ := Arrow.mk (i ≫ v))
    (A₃ := Arrow.mk (affineLineCylinder.map j)) (A₄ := Arrow.mk j)
    a b c d q ε e.hom (relativeLineProjection_comp_arrow k j i l v hi hl) hε he
  exact (congrArg (· ≫ e.hom) ht).trans (hc.trans (congrArg (ε.inv ≫ ·) hp.symm))

end AlgebraicGeometry.MotivicHomotopy
