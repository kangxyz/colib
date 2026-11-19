/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.Restriction
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.PointSupport.OpenRestriction
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Strata
import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.Support

/-! # Open restriction of a coniveau stratum -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite Order TopologicalSpace
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

attribute [local instance] specializationOrder

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

variable {Y X : Sm(k)} (f : Y ⟶ X) [IsOpenImmersion f.left] {p : ℕ}

/-- The original open immersion takes a point to a point of the same codimension. -/
abbrev coniveauPointImage (y : ConiveauPoints k Y p) : ConiveauPoints k X p :=
  ⟨f.left y.1, (Topology.IsOpenEmbedding.coheight_eq (x := y.1)
    f.left f.left.isOpenEmbedding).trans y.2⟩

private theorem pointWindowNeighborhood_image {y : Y.left}
    (ZW : ConiveauSupportPairs k X p (p + 1)) (U : PointSupportNeighborhoods k Y y)
    (hU : PointWindowNeighborhood k Y ((coniveauSupportPairsPreimage k f p (p + 1)).obj ZW) U) :
    PointWindowNeighborhood k X ZW ((pointSupportImageNeighborhoods k f y).obj U) := by
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    exact hU.1 ha
  · change pointSupportComplement k X (f.left y) (f.left ''ᵁ U.1) ≤ ZW.1.2.1.compl
    rw [← image_pointSupportComplement k f y U.1]
    rintro _ ⟨a, ha, rfl⟩
    exact hU.2 ha

@[reassoc]
private theorem pointWindowNeighborhoodArrowMap_right_comp {T : Sm(k)} {y : T.left}
    (ZW : ConiveauSupportPairs k T p (p + 1)) (U : PointSupportNeighborhoods k T y)
    (hU : PointWindowNeighborhood k T ZW U) :
    (pointWindowNeighborhoodArrowMap k T ZW U hU).right ≫
      supportOpenInclusion k T ZW.1.1.1 = SmoothSite.openInclusion T U.1 :=
  MorphismProperty.Over.Hom.ext (T.left.homOfLE_ι hU.1)

private theorem pointWindowNeighborhoodArrowMap_openRestriction {y : Y.left}
    (ZW : ConiveauSupportPairs k X p (p + 1)) (U : PointSupportNeighborhoods k Y y)
    (hU : PointWindowNeighborhood k Y ((coniveauSupportPairsPreimage k f p (p + 1)).obj ZW) U) :
    pointWindowNeighborhoodArrowMap k Y _ U hU ≫ supportPairPreimageMap k f ZW =
      (pointSupportImagePairIso k f y U).hom ≫
        pointWindowNeighborhoodArrowMap k X ZW ((pointSupportImageNeighborhoods k f y).obj U)
          (pointWindowNeighborhood_image k f ZW U hU) := by
  let : IsOpenImmersion ((coniveauSupportPairsInclusion k X p (p + 1)).obj (op ZW)).hom.left :=
    inferInstanceAs (IsOpenImmersion (supportOpenMap k X ZW.2).left)
  apply openPairArrowMap_eq_of_right
  let a := supportOpenInclusion k X ZW.1.1.1
  let : Mono a := (SmoothSite.forgetScheme _).mono_of_mono_map
    (inferInstanceAs (Mono (Scheme.Opens.ι (X := X.left) ZW.1.1.1.compl)))
  apply (cancel_mono a).mp
  change (_ ≫ supportOpenPreimageMap k f ZW.1.1.1) ≫ _ =
    ((pointSupportImagePairIso k f y U).hom.right ≫ _) ≫ _
  simp only [Category.assoc, supportOpenPreimageMap_comp_inclusion, a,
    pointWindowNeighborhoodArrowMap_right_comp, pointSupportImagePairIso_hom_right_comp]
  exact pointWindowNeighborhoodArrowMap_right_comp_assoc k _ U hU f

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] effectivePairCohomology

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [UnivLE.{u, w'}]

local notation "DM(" field ")" => EffectiveMotivesMinus field

/-- Open restriction commutes with taking a component at a point of the open. -/
@[reassoc]
theorem coniveauWindowPointProjection_openRestriction (K : DM(k)) (n : ℤ)
    (y : ConiveauPoints k Y p) :
    coniveauRelativeSupportRestrict k K n p (p + 1) f ≫ coniveauWindowPointProjection k Y K n y =
      coniveauWindowPointProjection k X K n (coniveauPointImage k f y) ≫
        (pointSupportOpenRestrictionIso k f K n y.1).hom := by
  apply colimit.hom_ext
  intro ZW
  let ZW' := (coniveauSupportPairsPreimage k f p (p + 1)).obj ZW
  obtain ⟨U, hU⟩ := exists_pointWindowNeighborhood k Y y ZW'
  let V := (pointSupportImageNeighborhoods k f y.1).obj U
  have hV := pointWindowNeighborhood_image k f ZW U hU
  rw [ι_coniveauRelativeSupportRestrict_assoc, ι_coniveauWindowPointProjection k Y K n y ZW' U hU,
    ι_coniveauWindowPointProjection_assoc k X K n (coniveauPointImage k f y) ZW V hV]
  let H := effectivePairCohomology k K n
  let a := supportPairPreimageMap k f ZW
  let b := (pointSupportImagePairIso k f y.1 U).hom
  let l := pointWindowNeighborhoodArrowMap k Y ZW' U hU
  let r := pointWindowNeighborhoodArrowMap k X ZW V hV
  have hab : l ≫ a = b ≫ r := pointWindowNeighborhoodArrowMap_openRestriction k f ZW U hU
  let DX := coniveauRelativeSupportDiagram k X K n p (p + 1)
  let DY := coniveauRelativeSupportDiagram k Y K n p (p + 1)
  let GX := pointSupportCohomologyDiagram k X K n (f.left y.1)
  let GY := pointSupportCohomologyDiagram k Y K n y.1
  let α : DX.obj ZW ⟶ DY.obj ZW' := H.map a.op
  let β : GX.obj (op V) ⟶ GY.obj (op U) := H.map b.op
  let l' : DY.obj ZW' ⟶ GY.obj (op U) := H.map l.op
  let r' : DX.obj ZW ⟶ GX.obj (op V) := H.map r.op
  let ιY := colimit.ι GY (op U)
  let ιX := colimit.ι GX (op V)
  let e := pointSupportOpenRestrictionIso k f K n y.1
  have hι : ιX ≫ e.hom = β ≫ ιY := pointSupportι_openRestrictionIso k f K n y.1 U
  have h : α ≫ l' = r' ≫ β := (H.map_comp a.op l.op).symm.trans
    ((H.congr_map (congrArg Quiver.Hom.op hab)).trans (H.map_comp r.op b.op))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ιY) h).trans
    ((Category.assoc _ _ _).trans (congrArg (r' ≫ ·) hι.symm)))

/-- The inclusion of a surviving point into the window restricts by its point isomorphism. -/
@[reassoc]
theorem pointSupportToConiveauWindow_openRestriction (K : DM(k)) (n : ℤ)
    (y : ConiveauPoints k Y p) :
    pointSupportToConiveauWindow k X K n (coniveauPointImage k f y) ≫
        coniveauRelativeSupportRestrict k K n p (p + 1) f =
      (pointSupportOpenRestrictionIso k f K n y.1).hom ≫
        pointSupportToConiveauWindow k Y K n y := by
  apply coniveauWindow_hom_ext
  intro z
  rw [Category.assoc, coniveauWindowPointProjection_openRestriction, ← Category.assoc,
    Category.assoc (pointSupportOpenRestrictionIso k f K n y.1).hom]
  by_cases h : y = z
  · subst z
    simp
  · have h' : coniveauPointImage k f y ≠ coniveauPointImage k f z := fun he ↦
      h (Subtype.ext (f.left.isOpenEmbedding.injective (congrArg Subtype.val he)))
    rw [pointSupportToConiveauWindow_projection_of_ne k X K n h', zero_comp,
      pointSupportToConiveauWindow_projection_of_ne k Y K n h, comp_zero]

/-- A summand indexed by a point outside the open has zero restriction. -/
@[reassoc]
theorem pointSupportToConiveauWindow_openRestriction_eq_zero (K : DM(k)) (n : ℤ)
    (x : ConiveauPoints k X p) (hx : x.1 ∉ Set.range f.left) :
    pointSupportToConiveauWindow k X K n x ≫ coniveauRelativeSupportRestrict k K n p (p + 1) f =
      0 := by
  apply coniveauWindow_hom_ext
  intro y
  have hxy : x ≠ coniveauPointImage k f y := fun h ↦
    hx ⟨y.1, (congrArg Subtype.val h).symm⟩
  rw [Category.assoc, coniveauWindowPointProjection_openRestriction, ← Category.assoc,
    pointSupportToConiveauWindow_projection_of_ne k X K n hxy, zero_comp, zero_comp]

end AlgebraicGeometry.MotivicHomotopy
