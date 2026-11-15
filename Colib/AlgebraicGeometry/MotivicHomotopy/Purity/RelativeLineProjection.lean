/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Nested
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.LaurentCochain
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffinePairContraction
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.RelativeLineCover

/-! # The original affine and Laurent projections of a relative line -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite SmoothSite.Contraction

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

private theorem map_split_id {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y : C} {f : X ⟶ Y} {g : Y ⟶ X} (h : f ≫ g = 𝟙 X) :
    F.map f ≫ F.map g = 𝟙 (F.obj X) :=
  (F.map_comp f g).symm.trans ((F.congr_map h).trans (F.map_id X))

private theorem map_split_projector {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y : C} {f : X ⟶ Y} {g : Y ⟶ X} {p : X ⟶ X} (h : f ≫ g = p) :
    F.map f ≫ F.map g = F.map p :=
  (F.map_comp f g).symm.trans (F.congr_map h)

private def mapIsoCompData {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y Z : C} (e : X ≅ Y) (f : F.obj Y ⟶ F.obj Z) (hf : IsIso f) :
    { d : F.obj X ≅ F.obj Z // d.hom = F.map e.hom ≫ f } :=
  ⟨F.mapIso e ≪≫ @asIso _ _ _ _ f hf, rfl⟩

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S
local notation "A" => SmoothSite.additiveGroupObject S
local notation "G" => SmoothSite.multiplicativeGroupObject S

/-- The map of open pairs induced by the original Laurent unit. -/
abbrev relativeLaurentUnitArrow {U X : Sm} (j : U ⟶ X) :
    Arrow.mk j ⟶ Arrow.mk (torusCylinder.map j) :=
  Arrow.homMk' (unitSection.app U) (unitSection.app X) (unitSection.naturality j).symm

/-- The map of open pairs induced by the original Laurent projection. -/
abbrev relativeLaurentProjectionArrow {U X : Sm} (j : U ⟶ X) :
    Arrow.mk (torusCylinder.map j) ⟶ Arrow.mk j :=
  Arrow.homMk' ((projection G).app U) ((projection G).app X) ((projection G).naturality j).symm

private theorem relativeLaurentUnit_projection_arrow {U X : Sm} (j : U ⟶ X) :
    relativeLaurentUnitArrow k j ≫ relativeLaurentProjectionArrow k j = 𝟙 (Arrow.mk j) := by
  apply Arrow.hom_ext
  · exact unitSection_projection U
  · exact unitSection_projection X

private theorem relativeLaurentProjection_unit_arrow {U X : Sm} (j : U ⟶ X) :
    relativeLaurentProjectionArrow k j ≫ relativeLaurentUnitArrow k j =
      laurentPairProjector k (Arrow.mk j) := by
  apply Arrow.hom_ext <;> rfl

variable {U X W : SmoothSite (Spec (CommRingCat.of k))} (j : U ⟶ X)
  (i : affineLineCylinder.obj U ⟶ W) (l : torusCylinder.obj X ⟶ W)
  (v : W ⟶ affineLineCylinder.obj X)
  [IsOpenImmersion v.left]
  (hi : i ≫ v = affineLineCylinder.map j) (hl : l ≫ v = openInclusion.app X)

/-- The literal equality of affine inclusions, as an isomorphism of pairs. -/
def relativeLineAffineArrowIso :
    Arrow.mk (i ≫ v) ≅ Arrow.mk (affineLineCylinder.map j) :=
  Arrow.isoMk' (i ≫ v) (affineLineCylinder.map j) (Iso.refl _) (Iso.refl _) (by
    change 𝟙 (affineLineCylinder.obj U) ≫ affineLineCylinder.map j =
      (i ≫ v) ≫ 𝟙 (affineLineCylinder.obj X)
    exact (Category.id_comp _).trans (hi.symm.trans (Category.comp_id _).symm))

/-- The first nested map on the original inclusions. -/
abbrev relativeLineNestedArrow : Arrow.mk i ⟶ Arrow.mk (i ≫ v) :=
  let s := nestedPairFirstSquare k i v
  Arrow.homMk' s.f₁₂ s.f₃₄ s.fac

/-- The original projection from the affine cylinder as a map of pairs. -/
abbrev relativeLineAffineProjectionArrow :
    Arrow.mk (affineLineCylinder.map j) ⟶ Arrow.mk j :=
  let s := SmoothSite.affinePairProjectionSquare j
  Arrow.homMk' s.f₁₂ s.f₃₄ s.fac

/-- The composite of the four original pair maps is the Laurent projection. -/
theorem relativeLineProjection_comp_arrow :
    relativeLineLaurentArrow k j i l v hi hl ≫ relativeLineNestedArrow k i v ≫
      (relativeLineAffineArrowIso k j i v hi).hom ≫ relativeLineAffineProjectionArrow k j =
        relativeLaurentProjectionArrow k j := by
  apply Arrow.hom_ext
  · change (SmoothSite.Contraction.openInclusion.app U) ≫ 𝟙 _ ≫ 𝟙 _ ≫
      (projection A).app U = (projection G).app U
    simpa only [Category.id_comp] using openInclusion_projection U
  · change l ≫ v ≫ 𝟙 _ ≫ (projection A).app X = (projection G).app X
    rw [Category.id_comp, ← Category.assoc, hl, openInclusion_projection]

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "P" => effectivePairMotiveFunctor k

/-- The canonical abelian structure on sheaves with transfers. -/
local instance instAbelianRelativeLineThom : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

set_option maxHeartbeats 600000 in
-- Apply the pair functor to the original split relation.
/-- The native relative Laurent projection is split by the native unit. -/
theorem relativeLaurentUnit_projection :
    let s := relativeLaurentUnitArrow k j
    let r := relativeLaurentProjectionArrow k j
    let F := P
    F.map s ≫ F.map r = 𝟙 (F.obj (Arrow.mk j)) := by
  intro s r F
  exact map_split_id F (relativeLaurentUnit_projection_arrow k j)

set_option maxHeartbeats 1000000 in
-- Apply the pair functor to the original projector relation.
/-- On the literal Laurent pair the projector is the composite of the
original relative projection and unit. -/
theorem relativeLaurentProjection_unit :
    let s := relativeLaurentUnitArrow k j
    let r := relativeLaurentProjectionArrow k j
    let F := P
    F.map r ≫ F.map s = F.map (laurentPairProjector k (Arrow.mk j)) := by
  intro s r F
  exact map_split_projector F (relativeLaurentProjection_unit_arrow k j)

variable [IsOpenImmersion j.left]

set_option maxHeartbeats 900000 in
-- Fix the two literal smooth-site endpoints before reflecting the affine projection.
/-- The affine comparison and its map on the original pair. -/
@[no_expose]
def relativeLineAffineComparisonData := by
  let Q := P
  let e := relativeLineAffineArrowIso k j i v hi
  let d := effectivePairMotiveMap k (SmoothSite.affinePairProjectionSquare j)
  have hd : IsIso d := isIso_effectivePairMotiveMap_affinePairProjection k j
  exact mapIsoCompData Q (Z := Arrow.mk j) e d hd

/-- The middle term uses the quotient of the literal affine cylinder. -/
def relativeLineAffineComparison :
    effectivePairMotive k (i ≫ v) ≅ effectivePairMotive k j :=
  (relativeLineAffineComparisonData k j i v hi).val

end AlgebraicGeometry.MotivicHomotopy
