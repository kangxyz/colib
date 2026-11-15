/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.LaurentRetract
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.RelativeLineNestedProjection
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ZeroSectionComplement
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.Support
import Colib.CategoryTheory.Triangulated.SplitProjectionBoundary
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# One more trivial line on the original relative motive

For a pair `(X,U)`, the union of `U × A¹` and `X × Gₘ` is the open
complement of the old support times the zero section. The nested-open
triangle and open-cover excision give a boundary to the original Laurent
pair. Projection to the reduced summand gives the one-line Thom map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

attribute [local irreducible] Cor.graphFunctor transferRepresentable

private theorem isIso_boundaryOfSplitProjection {C : Type*} [Category* C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) {B Y R : C}
    (e : T.obj₂ ≅ B) (ε : Y ≅ T.obj₁) (r : Retract R Y) (p : Y ⟶ B) (s : B ⟶ Y)
    (hp : T.mor₁ ≫ e.hom = ε.inv ≫ p) (hs : s ≫ p = 𝟙 B)
    (hr : r.r ≫ r.i = 𝟙 Y - p ≫ s) :
    IsIso (T.mor₃ ≫ (ε.inv ≫ r.r)⟦(1 : ℤ)⟧') := by
  let p' := ε.inv ≫ p
  let s' := s ≫ ε.hom
  let q' := ε.inv ≫ r.r
  let i' := r.i ≫ ε.hom
  have hps : s' ≫ p' = 𝟙 _ := by simp only [p', s', Category.assoc, Iso.hom_inv_id_assoc, hs]
  have hiq : i' ≫ q' = 𝟙 _ := by
    simp only [i', q', Category.assoc, Iso.hom_inv_id_assoc, r.retract]
  have hqi : q' ≫ i' = 𝟙 _ - p' ≫ s' := calc
    _ = ε.inv ≫ (r.r ≫ r.i) ≫ ε.hom := by simp only [q', i', Category.assoc]
    _ = ε.inv ≫ (𝟙 Y - p ≫ s) ≫ ε.hom := congrArg (fun x => ε.inv ≫ x ≫ ε.hom) hr
    _ = _ := by
      simp only [p', s', Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub,
        Iso.inv_hom_id, Category.assoc]
  exact isIso_boundary_reducedProjection T.mor₁ e T.mor₂ T.mor₃ p' s' q' i' hp hps hiq hqi hT

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S
variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "P" => effectivePairMotiveFunctor k

/-- The canonical abelian structure on sheaves with transfers. -/
local instance instAbelianRelativeLineThomBoundary : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

variable {U X W : SmoothSite (Spec (CommRingCat.of k))} (j : U ⟶ X)
  (i : affineLineCylinder.obj U ⟶ W) (l : torusCylinder.obj X ⟶ W)
  (v : W ⟶ affineLineCylinder.obj X)
  (hi : i ≫ v = affineLineCylinder.map j) (hl : l ≫ v = openInclusion.app X)

variable [IsOpenImmersion j.left] [IsOpenImmersion v.left]
  [IsOpenImmersion i.left] [IsOpenImmersion l.left]
  (hpb : (relativeLineOpenCoverSquare k j i l v hi hl).IsPullback)
  (hcover : Set.range i.left ∪ Set.range l.left = Set.univ)

local notation "T" => effectiveNestedPairTriangle k i v

variable [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]

set_option maxHeartbeats 900000 in
-- Keep the original signed shifted projection as a named morphism.
/-- The relative line Thom map is the native boundary followed by the shifted
projection to the original reduced Laurent summand. -/
def relativeLineThomMorphism :
    effectivePairMotive k v ⟶
      ((effectiveReducedTorusTensorFunctor k).obj (effectivePairMotive k j))⟦(1 : ℤ)⟧ :=
  effectiveNestedPairBoundary k i v ≫
    ((relativeLineLaurentComparison k j i l v hi hl hpb hcover).inv ≫
      (effectiveRelativeLaurentRetract k j).r)⟦(1 : ℤ)⟧'

set_option maxHeartbeats 1000000 in
-- Apply the abstract split boundary to the two original comparisons.
private theorem isIso_relativeLineThomMorphism_of_split
    (p : effectivePairMotive k (torusCylinder.map j) ⟶ effectivePairMotive k j)
    (s : effectivePairMotive k j ⟶ effectivePairMotive k (torusCylinder.map j))
    (hp : (T).mor₁ ≫ (relativeLineAffineComparison k j i v hi).hom =
      (relativeLineLaurentComparison k j i l v hi hl hpb hcover).inv ≫ p)
    (hs : s ≫ p = 𝟙 _)
    (hr :
      let r := effectiveRelativeLaurentRetract k j
      r.r ≫ r.i = 𝟙 _ - p ≫ s) :
    IsIso (relativeLineThomMorphism k j i l v hi hl hpb hcover) :=
  isIso_boundaryOfSplitProjection (T) (effectiveNestedPairTriangle_distinguished k i v)
    (relativeLineAffineComparison k j i v hi)
    (relativeLineLaurentComparison k j i l v hi hl hpb hcover)
    (effectiveRelativeLaurentRetract k j) p s hp hs hr

set_option maxHeartbeats 1100000 in
-- The original projector identity is transported along the two specified split maps.
private theorem relativeLineLaurentProjector
    (p : effectivePairMotive k (torusCylinder.map j) ⟶ effectivePairMotive k j)
    (s : effectivePairMotive k j ⟶ effectivePairMotive k (torusCylinder.map j))
    (hp : p = (P).map (relativeLaurentProjectionArrow k j))
    (hs : s = (P).map (relativeLaurentUnitArrow k j)) :
    let r := effectiveRelativeLaurentRetract k j
    r.r ≫ r.i = 𝟙 _ - p ≫ s := by
  intro r
  let A := effectivePairMotive k (torusCylinder.map j)
  let q : A ⟶ A := (P).map (laurentPairProjector k (Arrow.mk j))
  have hps : p ≫ s = q :=
    (congrArg₂ (fun p' s' => p' ≫ s') hp hs).trans (relativeLaurentProjection_unit k j)
  have h : r.r ≫ r.i = 𝟙 A - q := effectiveRelativeLaurentRetract_projector k j
  exact h.trans (congrArg (fun f : A ⟶ A => 𝟙 A - f) hps.symm)

set_option maxHeartbeats 1450000 in
-- Supply the actual split projections and the already identified first map.
/-- The indicated signed boundary gives an isomorphism onto the shifted reduced summand. -/
theorem isIso_relativeLineThomMorphism :
    IsIso (relativeLineThomMorphism k j i l v hi hl hpb hcover) := by
  let F := P
  let A := effectivePairMotive k (torusCylinder.map j)
  let B := effectivePairMotive k j
  let p : A ⟶ B := F.map (relativeLaurentProjectionArrow k j)
  let s : B ⟶ A := F.map (relativeLaurentUnitArrow k j)
  have n := relativeLineNestedFirst k j i l v hi hl hpb hcover p rfl
  have hs := relativeLaurentUnit_projection k j
  have hr := relativeLineLaurentProjector k j p s rfl rfl
  exact isIso_relativeLineThomMorphism_of_split k j i l v hi hl hpb hcover p s n hs hr

set_option maxHeartbeats 900000 in
-- Keep the supported motive and shift in the statement.
/-- Adding a literal trivial line to an open pair shifts the actual
reduced Laurent summand by one, via its original localization boundary. -/
def relativeLineThomIso :
    effectivePairMotive k v ≅
      ((effectiveReducedTorusTensorFunctor k).obj (effectivePairMotive k j))⟦(1 : ℤ)⟧ :=
  @asIso _ _ _ _ (relativeLineThomMorphism k j i l v hi hl hpb hcover)
    (isIso_relativeLineThomMorphism k j i l v hi hl hpb hcover)

set_option maxHeartbeats 750000 in
-- Compare the two projections on the literal original hom type.
/-- The relative isomorphism has the original signed boundary as its forward map. -/
theorem relativeLineThomIso_hom :
    (relativeLineThomIso k j i l v hi hl hpb hcover).hom =
      relativeLineThomMorphism k j i l v hi hl hpb hcover := by
  unfold relativeLineThomIso
  rfl

local instance instNoetherianRelativeLineThom :
    IsNoetherian (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) :=
  inferInstanceAs (IsNoetherian (Spec (CommRingCat.of k)))

set_option maxHeartbeats 950000 in
-- Install the original affine and Laurent charts on the marked support.
/-- The Thom isomorphism for adding one zero coordinate to the original closed support. -/
def effectiveAppendZeroSectionThomIso
    {Z Y : SmoothSite (Spec (CommRingCat.of k))} (z : Z ⟶ Y) [IsClosedImmersion z.left] :=
  let R := CommRingCat.of k
  relativeLineThomIso k (closedPairOpenInclusion z.left)
    (appendZeroAffineOpen R z) (appendZeroLaurentOpen R z)
    (closedPairOpenInclusion (appendZeroSection R z).left)
    (appendZeroAffineOpen_comp R z) (appendZeroLaurentOpen_comp R z)
    (appendZeroOpen_isPullback R z) (appendZeroOpen_range_cover R z)

end AlgebraicGeometry.MotivicHomotopy
