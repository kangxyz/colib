/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.DeformationPairBaseChange
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.PairOpenCover

/-!
# Restricting the original deformation fibre maps to opens

Over an affine open of the ambient scheme, base change of the extended
Rees algebra gives an isomorphism with the restricted deformation.
The two open-pair comparisons identify the original fibre maps before
and after this restriction.
-/

public noncomputable section

set_option quotPrecheck false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.SmoothSite
open Stacks.Deformation

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

attribute [local irreducible] Cor.graphFunctor transferRepresentable

section RestrictedComparison

variable {Z X : Sm(k)} (i : Z ⟶ X) [IsClosedImmersion i.left]

variable {k} in
/-- Restrict the original closed immersion to an open of its ambient scheme. -/
abbrev restrictClosedImmersion (U : X.left.Opens) :
    (opensFunctor Z).obj (i.left ⁻¹ᵁ U) ⟶ (opensFunctor X).obj U := preimageOpenMap X i U

omit [IsClosedImmersion i.left] in
variable {k} in
/-- The restricted closed immersion is the pullback along the actual open inclusion. -/
theorem restrictClosedImmersion_isPullback (U : X.left.Opens) :
    IsPullback (restrictClosedImmersion i U).left
      (openInclusion Z (i.left ⁻¹ᵁ U)).left (openInclusion X U).left i.left := by
  change IsPullback (i.left.resLE U (i.left ⁻¹ᵁ U) le_rfl) _ _ _
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact isPullback_morphismRestrict i.left U

variable {k} in
instance restrictClosedImmersion_isClosedImmersion (U : X.left.Opens) :
    IsClosedImmersion (restrictClosedImmersion i U).left :=
  MorphismProperty.of_isPullback (restrictClosedImmersion_isPullback i U).flip inferInstance

variable {k} in
/-- The open of the deformation lying over the indicated ambient open. -/
abbrev deformationBaseOpen (U : X.left.Opens) : (closedPairDeformation i).left.Opens :=
  deformationAmbientProjection i ⁻¹ᵁ U

private def smoothIsoOfOpenRange {Y X : Sm(k)} (a : Y ⟶ X) [IsOpenImmersion a.left]
    (V : X.left.Opens) (h : Set.range a.left = (V : Set X.left)) :
    Y ≅ (opensFunctor X).obj V :=
  let e := IsOpenImmersion.isoOfRangeEq a.left V.ι (h.trans (Scheme.Opens.range_ι V).symm)
  MorphismProperty.Over.isoMk e (by
    change e.hom ≫ V.ι ≫ X.hom = Y.hom
    rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, MorphismProperty.Over.w a])

private theorem smoothIsoOfOpenRange_comp {Y X : Sm(k)} (a : Y ⟶ X) [IsOpenImmersion a.left]
    (V : X.left.Opens) (h : Set.range a.left = (V : Set X.left)) :
    (smoothIsoOfOpenRange k a V h).hom ≫ openInclusion X V = a := by
  apply MorphismProperty.Over.Hom.ext
  exact IsOpenImmersion.isoOfRangeEq_hom_fac a.left V.ι (h.trans (Scheme.Opens.range_ι V).symm)

private theorem openBaseChangeArrow_mono {U U' Y Y' : Sm(k)} {j : U ⟶ Y} {l : U' ⟶ Y'}
    (a : U' ⟶ U) (b : Y' ⟶ Y) (h : a ≫ j = l ≫ b)
    [IsOpenImmersion a.left] [IsOpenImmersion b.left] :
    Mono (Arrow.homMk' a b h) := by
  let : Mono a := (forgetScheme _).mono_of_mono_map (inferInstanceAs (Mono a.left))
  let : Mono b := (forgetScheme _).mono_of_mono_map (inferInstanceAs (Mono b.left))
  constructor
  intro A f g w
  apply Arrow.hom_ext
  · exact (cancel_mono a).1 (congrArg Arrow.Hom.left w)
  · exact (cancel_mono b).1 (congrArg Arrow.Hom.right w)

private def openBaseChangeIso {U U' Y Y' : Sm(k)} {j : U ⟶ Y} {l : U' ⟶ Y'}
    (a : U' ⟶ U) (b : Y' ⟶ Y) [IsOpenImmersion b.left]
    (h : IsPullback l.left a.left b.left j.left) (V : Y.left.Opens)
    (e : Set.range b.left = (V : Set Y.left)) :
    Arrow.mk l ≅ Arrow.mk (preimageOpenMap Y j V) := by
  let r := smoothIsoOfOpenRange k b V e
  have hr : r.hom ≫ openInclusion Y V = b := smoothIsoOfOpenRange_comp k b V e
  let : IsOpenImmersion a.left := MorphismProperty.of_isPullback h inferInstance
  have hpre : Set.range a.left = ((j.left ⁻¹ᵁ V : U.left.Opens) : Set U.left) := by
    rw [range_fst_of_cartesian h.flip, e, Scheme.Hom.coe_preimage]
  let t := smoothIsoOfOpenRange k a (j.left ⁻¹ᵁ V) hpre
  have ht : t.hom ≫ openInclusion U (j.left ⁻¹ᵁ V) = a :=
    smoothIsoOfOpenRange_comp k a (j.left ⁻¹ᵁ V) hpre
  refine Arrow.isoMk t r ?_
  let : Mono (openInclusion Y V) := (forgetScheme _).mono_of_mono_map (inferInstanceAs (Mono V.ι))
  apply (cancel_mono (openInclusion Y V)).1
  change (t.hom ≫ preimageOpenMap Y j V) ≫ openInclusion Y V =
    (l ≫ r.hom) ≫ openInclusion Y V
  rw [Category.assoc, restrictedOpenMap_comp_openInclusion, ← Category.assoc t.hom, ht,
    Category.assoc, hr]
  exact MorphismProperty.Over.Hom.ext h.w.symm

/-- The original diagram on complementary opens is cartesian in schemes. -/
theorem closedPairSquare_isPullback_scheme
    {X Y : Sm(k)} {Z W : Scheme.{u}} {z : Z ⟶ X.left} {w : W ⟶ Y.left}
    [IsClosedImmersion z] [IsClosedImmersion w] {f : X ⟶ Y} {g : Z ⟶ W}
    (h : IsPullback z g f.left w) :
    IsPullback (closedPairSquare h).f₁₃.left (closedPairSquare h).f₁₂.left
      (closedPairSquare h).f₃₄.left (closedPairSquare h).f₂₄.left := by
  have hcom : IsPullback (closedPairOpenMap h).left (closedPairOpenInclusion z).left
      (closedPairOpenInclusion w).left f.left := by
    refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
    · exact congrArg (fun a => a.left) (closedPairOpenMap_comm h).symm
    · apply SetLike.coe_injective
      rw [Scheme.Hom.coe_preimage, Scheme.Hom.coe_opensRange, Scheme.Hom.coe_opensRange]
      exact (range_closedPairOpenInclusion_preimage h).symm
  exact hcom.flip

private theorem openBaseChangeIso_comp {U U' Y Y' : Sm(k)} {j : U ⟶ Y} {l : U' ⟶ Y'}
    (a : U' ⟶ U) (b : Y' ⟶ Y) [IsOpenImmersion b.left]
    (h : IsPullback l.left a.left b.left j.left) (V : Y.left.Opens)
    (e : Set.range b.left = (V : Set Y.left)) :
    (openBaseChangeIso k a b h V e).hom ≫ pairArrowOpenInclusion j V =
      Arrow.homMk' a b (MorphismProperty.Over.Hom.ext h.w.symm) := by
  apply Arrow.hom_ext
  · let : IsOpenImmersion a.left := MorphismProperty.of_isPullback h inferInstance
    have hpre : Set.range a.left = ((j.left ⁻¹ᵁ V : U.left.Opens) : Set U.left) := by
      rw [range_fst_of_cartesian h.flip, e, Scheme.Hom.coe_preimage]
    exact smoothIsoOfOpenRange_comp k a (j.left ⁻¹ᵁ V) hpre
  · exact smoothIsoOfOpenRange_comp k b V e

private theorem pairArrowOpenInclusion_mono {U Y : Sm(k)} (j : U ⟶ Y) (V : Y.left.Opens) :
    Mono (pairArrowOpenInclusion j V) := by
  let : IsOpenImmersion (openInclusion U (j.left ⁻¹ᵁ V)).left :=
    inferInstanceAs (IsOpenImmersion (j.left ⁻¹ᵁ V).ι)
  let : IsOpenImmersion (openInclusion Y V).left := inferInstanceAs (IsOpenImmersion V.ι)
  exact openBaseChangeArrow_mono k (openInclusion U (j.left ⁻¹ᵁ V)) (openInclusion Y V)
    (restrictedOpenMap_comp_openInclusion Y j V _ le_rfl).symm

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "P" => effectivePairMotiveFunctor k

private theorem isIso_deformationMapOnOpen_of_restricted
    (F : Square Sm(k)) (G : Square Sm(k))
    (A : Arrow.mk F.f₁₃ ⟶ Arrow.mk G.f₁₃) (B : Arrow.mk F.f₂₄ ⟶ Arrow.mk G.f₂₄)
    (hA : IsPullback F.f₁₃.left A.left.left A.right.left G.f₁₃.left)
    (hB : IsPullback F.f₂₄.left B.left.left B.right.left G.f₂₄.left)
    [IsOpenImmersion A.right.left] [IsOpenImmersion B.right.left]
    (hcomm : pairSquareArrow F ≫ B = A ≫ pairSquareArrow G)
    (V : G.X₄.left.Opens)
    (hpre : Set.range A.right.left = (G.f₃₄.left ⁻¹ᵁ V : Set G.X₃.left))
    (hpost : Set.range B.right.left = (V : Set G.X₄.left))
    (hF : IsIso (effectivePairMotiveMap k F)) :
    IsIso (effectivePairMapOnOpen k G.f₁₃ G.f₂₄ G.f₁₂ G.f₃₄ G.fac V) := by
  let a := openBaseChangeIso k A.left A.right hA (G.f₃₄.left ⁻¹ᵁ V) hpre
  let b := openBaseChangeIso k B.left B.right hB V hpost
  let c := pairArrowOpenInclusion G.f₂₄ V
  let d := pairArrowOpenInclusion G.f₁₃ (G.f₃₄.left ⁻¹ᵁ V)
  let r := pairArrowMapOnOpen G.f₁₃ G.f₂₄ G.f₁₂ G.f₃₄ G.fac V
  have ha : a.hom ≫ d = A :=
    (openBaseChangeIso_comp k A.left A.right hA _ hpre).trans (Arrow.hom_ext _ _ rfl rfl)
  have hb : b.hom ≫ c = B :=
    (openBaseChangeIso_comp k B.left B.right hB V hpost).trans (Arrow.hom_ext _ _ rfl rfl)
  let : Mono c := pairArrowOpenInclusion_mono k G.f₂₄ V
  have hr : r ≫ c = d ≫ pairSquareArrow G :=
    pairArrowMapOnOpen_comp G.f₁₃ G.f₂₄ G.f₁₂ G.f₃₄ G.fac V
  have h : pairSquareArrow F ≫ b.hom = a.hom ≫ r := by
    apply (cancel_mono c).1
    calc
      _ = pairSquareArrow F ≫ B :=
        (Category.assoc _ _ _).trans (congrArg (pairSquareArrow F ≫ ·) hb)
      _ = A ≫ pairSquareArrow G := hcomm
      _ = a.hom ≫ d ≫ pairSquareArrow G :=
        (congrArg (· ≫ pairSquareArrow G) ha.symm).trans (Category.assoc _ _ _)
      _ = _ := (congrArg (a.hom ≫ ·) hr.symm).trans (Category.assoc _ _ _).symm
  rw [effectivePairMapOnOpen_eq_map]
  exact (isIso_map_arrow_iff_of_comparison (P) _ _ a.hom b.hom h inferInstance inferInstance).mp hF

/-- Comparison for the actual fibre-one arrow restricted over a base open. -/
theorem isIso_deformationOneMapOnOpen_of_restriction (U : X.left.Opens) [IsAffineHom U.ι]
    (H : IsIso (effectivePairMotiveMap k (deformationOneSquare (restrictClosedImmersion i U)))) :
    IsIso (effectivePairMapOnOpen k (deformationOneSquare i).f₁₃
      (deformationOneSquare i).f₂₄
      (deformationOneSquare i).f₁₂ (deformationOneSquare i).f₃₄ (deformationOneSquare i).fac
      (deformationBaseOpen i U)) := by
  let j := restrictClosedImmersion i U
  let a := openInclusion X U
  let b := openInclusion Z (i.left ⁻¹ᵁ U)
  let : IsAffineHom a.left := inferInstanceAs (IsAffineHom U.ι)
  let : IsOpenImmersion a.left := inferInstanceAs (IsOpenImmersion U.ι)
  let : Etale a.left := inferInstanceAs (Etale U.ι)
  let h : IsPullback j.left b.left a.left i.left := restrictClosedImmersion_isPullback i U
  let β := smoothDeformationBaseChange k h
  let F := deformationOneSquare j
  let G := deformationOneSquare i
  let : IsOpenImmersion G.f₂₄.left := inferInstanceAs
    (IsOpenImmersion (closedPairOpenInclusion (deformationSupportInclusion i).left).left)
  let A := closedPairSquare (f := a) h
  let : IsOpenImmersion A.f₃₄.left := inferInstanceAs (IsOpenImmersion a.left)
  let hD := smoothDeformationSupportBaseChange_isPullback k h
  let B := closedPairSquare (f := β) (z := (deformationSupportInclusion j).left)
    (w := (deformationSupportInclusion i).left) hD
  have hβ := isPullback_deformationMapOver_ambient k h
  let : IsOpenImmersion β.left := MorphismProperty.of_isPullback hβ.flip
    (inferInstance : IsOpenImmersion a.left)
  let : IsOpenImmersion B.f₃₄.left := inferInstanceAs (IsOpenImmersion β.left)
  have hr : F.f₃₄ ≫ B.f₃₄ = A.f₃₄ ≫ G.f₃₄ :=
    MorphismProperty.Over.Hom.ext (closedPairOneSection_deformationMapOver h)
  have hcomp : pairSquareArrow F ≫ pairSquareArrow B = pairSquareArrow A ≫ pairSquareArrow G :=
    pairSquareArrow_comm_of_ambient F G (pairSquareArrow A) (pairSquareArrow B) hr
  have hpre : Set.range (pairSquareArrow A).right.left =
      (G.f₃₄.left ⁻¹ᵁ deformationBaseOpen i U : Set G.X₃.left) := by
    change Set.range U.ι =
      (closedPairOneSection i.left ⁻¹ᵁ
        (deformationAmbientProjection i ⁻¹ᵁ U) : Set X.left)
    have hsec : closedPairOneSection i.left ≫ deformationAmbientProjection i = 𝟙 X.left :=
      closedPairOneSection_toAmbient i.left
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.comp_preimage, hsec, Scheme.Hom.id_preimage]
  have hpost : Set.range B.f₃₄.left =
      (deformationBaseOpen i U : Set (closedPairDeformation i).left) := by
    change Set.range (deformationMapOver h) = _
    rw [range_fst_of_cartesian hβ]
    change _ ⁻¹' Set.range U.ι = _
    rw [Scheme.Opens.range_ι]
    exact (Scheme.Hom.coe_preimage (U := _) _).symm
  let : IsOpenImmersion (pairSquareArrow A).right.left :=
    (show IsOpenImmersion A.f₃₄.left from inferInstance)
  let : IsOpenImmersion (pairSquareArrow B).right.left :=
    (show IsOpenImmersion B.f₃₄.left from inferInstance)
  exact isIso_deformationMapOnOpen_of_restricted k F G (pairSquareArrow A) (pairSquareArrow B)
    (closedPairSquare_isPullback_scheme k h)
    (closedPairSquare_isPullback_scheme k hD)
    hcomp (deformationBaseOpen i U) hpre hpost H

private theorem isIso_deformationZeroMapOnOpen_of_cartesian
    {Z' X' : Sm(k)} {j : Z' ⟶ X'} [IsClosedImmersion j.left]
    {a : X' ⟶ X} {b : Z' ⟶ Z}
    [IsOpenImmersion a.left]
    (h : IsPullback j.left b.left a.left i.left)
    (V : (closedPairDeformation i).left.Opens)
    (hV : Set.range (smoothDeformationBaseChange k h).left =
      (V : Set (closedPairDeformation i).left))
    (H : IsIso (effectivePairMotiveMap k (deformationZeroSquareOfSmooth j))) :
    IsIso (effectivePairMapOnOpen k (deformationZeroSquareOfSmooth i).f₁₃
      (deformationZeroSquareOfSmooth i).f₂₄ (deformationZeroSquareOfSmooth i).f₁₂
      (deformationZeroSquareOfSmooth i).f₃₄ (deformationZeroSquareOfSmooth i).fac V) := by
  let : Smooth (i.left ≫ X.hom) := smooth_closedPair_comp i
  let : Smooth (j.left ≫ X'.hom) := smooth_closedPair_comp j
  let α := smoothNormalFibreBaseChange k h
  let β := smoothDeformationBaseChange k h
  let F := deformationZeroSquareOfSmooth j
  let G := deformationZeroSquareOfSmooth i
  let : IsOpenImmersion G.f₂₄.left := inferInstanceAs
    (IsOpenImmersion (closedPairOpenInclusion (deformationSupportInclusion i).left).left)
  have hN : IsPullback F.f₃₄.left α.left β.left G.f₃₄.left :=
    isPullback_deformationNormalFibreMap h X.hom X'.hom
  have hZ : IsPullback (normalBundleZeroSectionOfSmooth j).left b.left α.left
      (normalBundleZeroSectionOfSmooth i).left :=
    isPullback_deformationNormalZeroSection h X.hom X'.hom
  let hD := smoothDeformationSupportBaseChange_isPullback k h
  let A := closedPairSquare (f := α) (z := (normalBundleZeroSectionOfSmooth j).left)
    (w := (normalBundleZeroSectionOfSmooth i).left) hZ
  let B := closedPairSquare (f := β) (z := (deformationSupportInclusion j).left)
    (w := (deformationSupportInclusion i).left) hD
  have hβ : IsPullback β.left (deformationAmbientProjection j)
      (deformationAmbientProjection i) a.left := isPullback_deformationMapOver_ambient k h
  let hβOpen : IsOpenImmersion β.left :=
    MorphismProperty.of_isPullback hβ.flip (inferInstance : IsOpenImmersion a.left)
  let hαOpen : IsOpenImmersion α.left := MorphismProperty.of_isPullback hN hβOpen
  let A' : Arrow.mk F.f₁₃ ⟶ Arrow.mk G.f₁₃ := pairSquareArrow A
  let B' : Arrow.mk F.f₂₄ ⟶ Arrow.mk G.f₂₄ := pairSquareArrow B
  let : IsOpenImmersion A'.right.left := hαOpen
  let : IsOpenImmersion B'.right.left := hβOpen
  have hr : F.f₃₄ ≫ B'.right = A'.right ≫ G.f₃₄ :=
    MorphismProperty.Over.Hom.ext hN.w
  have hpre : Set.range A'.right.left = (G.f₃₄.left ⁻¹ᵁ V : Set G.X₃.left) := by
    have hR : Set.range α.left = G.f₃₄.left ⁻¹' Set.range β.left :=
      range_fst_of_cartesian hN.flip
    have hT : G.f₃₄.left ⁻¹' Set.range β.left = (G.f₃₄.left ⁻¹ᵁ V : Set G.X₃.left) :=
      (congrArg (Set.preimage G.f₃₄.left) hV).trans
        (Scheme.Hom.coe_preimage (U := V) G.f₃₄.left).symm
    exact hR.trans hT
  have hA : IsPullback F.f₁₃.left A'.left.left A'.right.left G.f₁₃.left :=
    closedPairSquare_isPullback_scheme k hZ
  have hB : IsPullback F.f₂₄.left B'.left.left B'.right.left G.f₂₄.left :=
    closedPairSquare_isPullback_scheme k hD
  exact isIso_deformationMapOnOpen_of_restricted k F G A' B' hA hB
    (pairSquareArrow_comm_of_ambient F G A' B' hr) V hpre hV H

/-- Comparison for the actual normal-fibre arrow restricted over a base open. -/
theorem isIso_deformationZeroMapOnOpen_of_restriction (U : X.left.Opens) [IsAffineHom U.ι]
    (H : IsIso (effectivePairMotiveMap k
      (deformationZeroSquareOfSmooth (restrictClosedImmersion i U)))) :
    IsIso (effectivePairMapOnOpen k (deformationZeroSquareOfSmooth i).f₁₃
      (deformationZeroSquareOfSmooth i).f₂₄ (deformationZeroSquareOfSmooth i).f₁₂
      (deformationZeroSquareOfSmooth i).f₃₄ (deformationZeroSquareOfSmooth i).fac
      (deformationBaseOpen i U)) := by
  let a := openInclusion X U
  let b := openInclusion Z (i.left ⁻¹ᵁ U)
  let : IsOpenImmersion a.left := inferInstanceAs (IsOpenImmersion U.ι)
  let : IsAffineHom a.left := inferInstanceAs (IsAffineHom U.ι)
  let h : IsPullback (restrictClosedImmersion i U).left b.left a.left i.left :=
    restrictClosedImmersion_isPullback i U
  have hV : Set.range (smoothDeformationBaseChange k h).left =
      (deformationBaseOpen i U : Set (closedPairDeformation i).left) := by
    change Set.range (deformationMapOver h) = _
    rw [range_fst_of_cartesian (isPullback_deformationMapOver_ambient k h)]
    change _ ⁻¹' Set.range U.ι = _
    rw [Scheme.Opens.range_ι]
    exact (Scheme.Hom.coe_preimage (U := U) (deformationAmbientProjection i)).symm
  exact isIso_deformationZeroMapOnOpen_of_cartesian k i h (deformationBaseOpen i U) hV H

end RestrictedComparison

end AlgebraicGeometry.MotivicHomotopy
