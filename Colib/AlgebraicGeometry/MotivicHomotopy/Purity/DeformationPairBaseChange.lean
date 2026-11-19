/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.DeformationCylinder
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.DeformationBaseChange
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.PairExcision

/-!
# Étale comparisons of closed-pair deformation fibres

The original ambient deformation, its closed support and the normal
bundle admit cartesian base change diagrams. Excision transfers
invertibility across étale neighborhoods preserving the original centre.
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

attribute [local irreducible] Cor.graphFunctor transferRepresentable

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Sm(" field ")" =>
  AlgebraicGeometry.Scheme.SmoothSite (Spec (CommRingCat.of field))
local notation "P" => effectivePairMotiveFunctor k

section Etale

variable {Z X Z' X' : Sm(k)} {i : Z ⟶ X} {j : Z' ⟶ X'}
  [IsClosedImmersion i.left] [IsClosedImmersion j.left] {a : X' ⟶ X} {b : Z' ⟶ Z}
  (h : IsPullback j.left b.left a.left i.left) [Etale a.left]

/-- The original morphism of deformations under étale base change is over the field. -/
@[expose] def smoothDeformationBaseChange : closedPairDeformation j ⟶ closedPairDeformation i :=
  homMk (deformationMapOver h) (by
    change deformationMapOver h ≫
      (deformationSpaceToBase (Stacks.Conormal.coborderIdeal i.left) ≫
        i.left.coborderRange.ι ≫ X.hom) = _
    rw [← Category.assoc, deformationMapOver_toBase, Category.assoc,
      ← Category.assoc (coborderMapOver i.left j.left a.left), coborderMapOver_ι,
      Category.assoc, MorphismProperty.Over.w a]
    rfl)

omit [PerfectField k] [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)] [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
private theorem etale_deformationMapOver : Etale (deformationMapOver h) := by
  let f := coborderMapOver i.left j.left a.left
  have hf : Etale f := by
    have : IsIso i.left.coborderRange.ι := isIso_coborderRange_ι_of_isClosedImmersion i.left
    have : IsIso j.left.coborderRange.ι := isIso_coborderRange_ι_of_isClosedImmersion j.left
    have h₀ : f = j.left.coborderRange.ι ≫ a.left ≫ inv i.left.coborderRange.ι := by
      apply (cancel_mono i.left.coborderRange.ι).1
      rw [coborderMapOver_ι, Category.assoc, Category.assoc,
        IsIso.inv_hom_id, Category.comp_id]
    rw [h₀]
    infer_instance
  exact MorphismProperty.of_isPullback (isPullback_deformationMapOver_coborder h).flip hf

/-- The original map of arrows associated to a square of smooth schemes. -/
abbrev pairSquareArrow {S : Scheme.{u}} (sq : Square (SmoothSite S)) :
    Arrow.mk sq.f₁₃ ⟶ Arrow.mk sq.f₂₄ := Arrow.homMk' sq.f₁₂ sq.f₃₄ sq.fac

/-- Compatibility of maps of open pairs follows from compatibility on the ambient schemes. -/
theorem pairSquareArrow_comm_of_ambient {S : Scheme.{u}}
    (f g : Square (SmoothSite S))
    (a₀ : Arrow.mk f.f₁₃ ⟶ Arrow.mk g.f₁₃)
    (b₀ : Arrow.mk f.f₂₄ ⟶ Arrow.mk g.f₂₄)
    [IsOpenImmersion g.f₂₄.left]
    (hr : f.f₃₄ ≫ b₀.right = a₀.right ≫ g.f₃₄) :
    pairSquareArrow f ≫ b₀ = a₀ ≫ pairSquareArrow g := by
  apply Arrow.hom_ext
  · let : Mono g.f₂₄ := (forgetScheme S).mono_of_mono_map
      (inferInstanceAs (Mono g.f₂₄.left))
    apply (cancel_mono g.f₂₄).1
    change (f.f₁₂ ≫ b₀.left) ≫ g.f₂₄ = (a₀.left ≫ g.f₁₂) ≫ g.f₂₄
    have h₁ : b₀.left ≫ g.f₂₄ = f.f₂₄ ≫ b₀.right := Arrow.w b₀
    have h₂ : a₀.left ≫ g.f₁₃ = f.f₁₃ ≫ a₀.right := Arrow.w a₀
    rw [Category.assoc, Category.assoc, h₁, g.fac, ← Category.assoc f.f₁₂, f.fac,
      Category.assoc, hr, ← Category.assoc f.f₁₃, ← h₂, Category.assoc]
  · exact hr


/-- The native morphism of zero-ideal deformations, viewed over the original field. -/
@[expose] def smoothDeformationSupportBaseChange (b : Z' ⟶ Z) :
    deformationSupport Z' ⟶ deformationSupport Z := by
  let d := deformationCentreMap (b := b.left)
  have e : d ≫ deformationSpaceToBase (⊥ : Z.left.IdealSheafData) =
      deformationSpaceToBase (⊥ : Z'.left.IdealSheafData) ≫ b.left :=
    deformationMap_toBase b.left ⊥ ⊥ _
  refine homMk d ?_
  change d ≫ deformationSpaceToBase (⊥ : Z.left.IdealSheafData) ≫ Z.hom =
    deformationSpaceToBase (⊥ : Z'.left.IdealSheafData) ≫ Z'.hom
  rw [← Category.assoc, e, Category.assoc, MorphismProperty.Over.w b]

omit [PerfectField k] [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)] [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [Etale a.left] in
/-- The original support square for a flat base change of the deformation. -/
theorem smoothDeformationSupportBaseChange_isPullback [Flat a.left] :
    IsPullback (deformationSupportInclusion j).left (smoothDeformationSupportBaseChange k b).left
      (smoothDeformationBaseChange k h).left (deformationSupportInclusion i).left :=
  isPullback_deformationSupportMap_deformationMapOver h

include h in
/-- Excision on the deformation pair uses the original étale map, inducing
the actual base-change isomorphism of relative motives. -/
theorem isIso_effectivePairMotiveMap_deformationBaseChange [IsIso b.left] :
    IsIso (effectivePairMotiveMap k
      (closedPairSquare (f := smoothDeformationBaseChange k h)
        (z := (deformationSupportInclusion j).left) (w := (deformationSupportInclusion i).left)
        (smoothDeformationSupportBaseChange_isPullback k h))) := by
  have hb : IsIso b.left := inferInstance
  have : Flat b.left := inferInstance
  have hc : IsIso (deformationCentreMap (b := b.left)) :=
    (isPullback_deformationCentreMap (b := b.left)).isIso_fst_of_isIso hb
  let : IsIso (smoothDeformationSupportBaseChange k b).left := hc
  let : Etale (smoothDeformationBaseChange k h).left := etale_deformationMapOver k h
  exact isIso_effectivePairMotiveMap_closedPairSquare k
    (z := (deformationSupportInclusion j).left) (w := (deformationSupportInclusion i).left)
    (smoothDeformationSupportBaseChange_isPullback k h)

include h in
/-- An étale neighborhood inducing an isomorphism on the closed
centre detects invertibility of the original fibre-one comparison. -/
theorem isIso_effectivePairMotiveMap_deformationOne_iff_of_etale [IsIso b.left] :
    IsIso (effectivePairMotiveMap k (deformationOneSquare j)) ↔
      IsIso (effectivePairMotiveMap k (deformationOneSquare i)) := by
  let F := deformationOneSquare j
  let G := deformationOneSquare i
  let : IsOpenImmersion G.f₁₃.left := inferInstanceAs
    (IsOpenImmersion (closedPairOpenInclusion i.left).left)
  let : IsOpenImmersion G.f₂₄.left := inferInstanceAs
    (IsOpenImmersion (closedPairOpenInclusion (deformationSupportInclusion i).left).left)
  let A := closedPairSquare (f := a) h
  let B := closedPairSquare (f := smoothDeformationBaseChange k h)
    (z := (deformationSupportInclusion j).left) (w := (deformationSupportInclusion i).left)
    (smoothDeformationSupportBaseChange_isPullback k h)
  have ha : IsIso (effectivePairMotiveMap k A) :=
    isIso_effectivePairMotiveMap_closedPairSquare k h
  have hb : IsIso (effectivePairMotiveMap k B) :=
    isIso_effectivePairMotiveMap_deformationBaseChange k h
  have hr : F.f₃₄ ≫ B.f₃₄ = A.f₃₄ ≫ G.f₃₄ := by
    apply MorphismProperty.Over.Hom.ext
    exact closedPairOneSection_deformationMapOver h
  let : IsOpenImmersion G.f₂₄.left := inferInstanceAs (IsOpenImmersion
    (closedPairOpenInclusion (deformationSupportInclusion i).left).left)
  exact isIso_map_arrow_iff_of_comparison (P) (pairSquareArrow F) (pairSquareArrow G)
    (pairSquareArrow A) (pairSquareArrow B)
    (pairSquareArrow_comm_of_ambient F G _ _ hr) ha hb

/-- The morphism of actual normal fibres retains their maps to the original field. -/
@[expose] def smoothNormalFibreBaseChange : normalBundleOfSmooth j ⟶ normalBundleOfSmooth i := by
  let : Smooth (i.left ≫ X.hom) := smooth_closedPair_comp i
  let : Smooth (j.left ≫ X'.hom) := smooth_closedPair_comp j
  let f := deformationNormalFibreMap h X.hom X'.hom
  refine homMk f ?_
  let π := (closedPairDeformation i).hom
  have hπ : (smoothDeformationBaseChange k h).left ≫ π = (closedPairDeformation j).hom :=
    MorphismProperty.Over.w (smoothDeformationBaseChange k h)
  have hN := (isPullback_deformationNormalFibreMap h X.hom X'.hom).w
  change f ≫ (normalBundleOfSmooth i).hom = (normalBundleOfSmooth j).hom
  have h₁ : normalBundleToDeformation i.left X.hom ≫ π = (normalBundleOfSmooth i).hom :=
    MorphismProperty.Over.w (deformationNormalMapOfSmooth i)
  have h₂ : normalBundleToDeformation j.left X'.hom ≫ (closedPairDeformation j).hom =
      (normalBundleOfSmooth j).hom := MorphismProperty.Over.w (deformationNormalMapOfSmooth j)
  have h₃ : deformationMapOver h ≫ π = (closedPairDeformation j).hom := hπ
  dsimp only [f]
  rw [← h₁, ← Category.assoc, ← hN, Category.assoc, h₃, h₂]

include h in
/-- An étale neighborhood inducing an isomorphism on the closed centre
detects invertibility of the actual normal-fibre comparison. -/
theorem isIso_effectivePairMotiveMap_deformationZero_iff_of_etale [IsIso b.left] :
    IsIso (effectivePairMotiveMap k (deformationZeroSquareOfSmooth j)) ↔
      IsIso (effectivePairMotiveMap k (deformationZeroSquareOfSmooth i)) := by
  let : Smooth (i.left ≫ X.hom) := smooth_closedPair_comp i
  let : Smooth (j.left ≫ X'.hom) := smooth_closedPair_comp j
  let F := deformationZeroSquareOfSmooth j
  let G := deformationZeroSquareOfSmooth i
  let f := smoothNormalFibreBaseChange k h
  have hA : IsPullback (normalBundleZeroSectionOfSmooth j).left b.left f.left
      (normalBundleZeroSectionOfSmooth i).left :=
    isPullback_deformationNormalZeroSection h X.hom X'.hom
  let A := closedPairSquare (f := f) (z := (normalBundleZeroSectionOfSmooth j).left)
    (w := (normalBundleZeroSectionOfSmooth i).left) hA
  let B := closedPairSquare (f := smoothDeformationBaseChange k h)
    (z := (deformationSupportInclusion j).left) (w := (deformationSupportInclusion i).left)
    (smoothDeformationSupportBaseChange_isPullback k h)
  let : Etale f.left := MorphismProperty.of_isPullback
    (isPullback_deformationNormalFibreMap h X.hom X'.hom)
    (etale_deformationMapOver k h)
  have ha : IsIso (effectivePairMotiveMap k A) :=
    isIso_effectivePairMotiveMap_closedPairSquare k
      (z := (normalBundleZeroSectionOfSmooth j).left)
      (w := (normalBundleZeroSectionOfSmooth i).left) hA
  have hb : IsIso (effectivePairMotiveMap k B) :=
    isIso_effectivePairMotiveMap_deformationBaseChange k h
  have hr : F.f₃₄ ≫ B.f₃₄ = A.f₃₄ ≫ G.f₃₄ := by
    apply MorphismProperty.Over.Hom.ext
    exact (isPullback_deformationNormalFibreMap h X.hom X'.hom).w
  let : IsOpenImmersion G.f₂₄.left := inferInstanceAs (IsOpenImmersion
    (closedPairOpenInclusion (deformationSupportInclusion i).left).left)
  exact isIso_map_arrow_iff_of_comparison (P) (pairSquareArrow F) (pairSquareArrow G)
    (pairSquareArrow A) (pairSquareArrow B)
    (pairSquareArrow_comm_of_ambient F G _ _ hr) ha hb

end Etale

/-- The projection from the original deformation to the ambient smooth scheme. -/
@[expose] def deformationAmbientProjection {S : Scheme.{u}} {Z X : SmoothSite S}
    (i : Z ⟶ X) [IsClosedImmersion i.left] :
    (closedPairDeformation i).left ⟶ X.left :=
  deformationSpaceToBase (Stacks.Conormal.coborderIdeal i.left) ≫ i.left.coborderRange.ι

/-- The deformation projection retains the original smooth-site structure map. -/
@[expose] def smoothDeformationAmbientProjection {S : Scheme.{u}} {Z X : SmoothSite S}
    (i : Z ⟶ X) [IsClosedImmersion i.left] : closedPairDeformation i ⟶ X :=
  homMk (deformationAmbientProjection i) (Category.assoc _ _ _)

/-- The ambient deformation projection restricts to the identity on the fibre at one. -/
theorem deformationOneMap_ambientProjection {S : Scheme.{u}} {Z X : SmoothSite S}
    (i : Z ⟶ X) [IsClosedImmersion i.left] :
    deformationOneMap i ≫ smoothDeformationAmbientProjection i = 𝟙 X := by
  apply MorphismProperty.Over.Hom.ext
  exact closedPairOneSection_toAmbient i.left

/-- On the original normal fibre the ambient projection factors through the centre. -/
theorem deformationNormalMap_ambientProjection {S : Scheme.{u}} {Z X : SmoothSite S}
    (i : Z ⟶ X) [IsClosedImmersion i.left] {n m : ℕ}
    (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m) :
    deformationNormalMapOfSmooth i ≫ smoothDeformationAmbientProjection i =
      normalBundleProjection i hX hZ ≫ i := by
  let := smooth_closedPair_comp i
  apply MorphismProperty.Over.Hom.ext
  exact normalBundleToDeformation_toAmbient i.left X.hom

omit [PerfectField k] [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)] [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
/-- Flat base change of the original ambient deformation projection is cartesian. -/
theorem isPullback_deformationMapOver_ambient {Z X Z' X' : Sm(k)}
    {i : Z ⟶ X} {j : Z' ⟶ X'} [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    {a : X' ⟶ X} {b : Z' ⟶ Z} (h : IsPullback j.left b.left a.left i.left) [Flat a.left] :
    IsPullback (deformationMapOver h) (deformationAmbientProjection j)
      (deformationAmbientProjection i) a.left := by
  let f := coborderMapOver i.left j.left a.left
  let : IsIso i.left.coborderRange.ι := isIso_coborderRange_ι_of_isClosedImmersion i.left
  let : IsIso j.left.coborderRange.ι := isIso_coborderRange_ι_of_isClosedImmersion j.left
  have hf : f = j.left.coborderRange.ι ≫ a.left ≫ inv i.left.coborderRange.ι := by
    apply (cancel_mono i.left.coborderRange.ι).1
    rw [coborderMapOver_ι, Category.assoc, Category.assoc,
        IsIso.inv_hom_id, Category.comp_id]
  let : Flat f := by rw [hf]; infer_instance
  have hc : IsPullback f j.left.coborderRange.ι i.left.coborderRange.ι a.left :=
    IsPullback.of_vert_isIso ⟨coborderMapOver_ι i.left j.left a.left⟩
  exact (isPullback_deformationMapOver_coborder h).paste_vert hc

end AlgebraicGeometry.MotivicHomotopy
