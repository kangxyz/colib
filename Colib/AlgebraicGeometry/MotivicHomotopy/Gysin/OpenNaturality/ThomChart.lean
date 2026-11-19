/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Gysin.OpenNaturality.Fibre
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.NormalBundleOrientation
import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffineSpaceThom
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # Open restriction of the normal-bundle chart classes -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme TopologicalSpace
open SmoothSite Contraction Stacks.Conormal Stacks.Deformation

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]

local instance openThomCorSheafify : HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

local instance openThomSmoothSheafify :
    HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S
local notation "Φ" => effectivePairMotiveFunctor k

attribute [local instance] normalBundleOrientationAbelian

attribute [local irreducible] Cor.graphFunctor SheafWithTransfers.transferRepresentable

/-- Restricting the normal pair to any open is its actual open inclusion,
including when written by way of the top element of the restriction diagram. -/
theorem relativeOpenRestrictionMotive_map_topIso_hom
    {A V Z : Sm} (p : V ⟶ Z) (j : A ⟶ V) [IsOpenImmersion j.left] (W : Z.left.Opens) :
    (relativeOpenRestrictionMotive k p j).map (homOfLE (le_top : W ≤ ⊤)) ≫
      (relativeOpenRestrictionTopIso k p j).hom =
      (Φ).map (pairArrowOpenInclusion j (p.left ⁻¹ᵁ W)) := by
  let f := (relativeOpenRestrictionPair k p j).map (homOfLE (le_top : W ≤ ⊤))
  change (Φ).map f ≫ (relativeOpenRestrictionTopIso k p j).hom = _
  rw [relativeOpenRestrictionTopIso_hom, ← (Φ).map_comp]
  apply (Φ).congr_map
  apply openPairArrowMap_eq_of_right
  apply MorphismProperty.Over.Hom.ext
  exact Scheme.homOfLE_ι V.left (p.left.preimage_mono (le_top : W ≤ ⊤))

section RestrictionMap

variable {Z X : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ X)
  [IsClosedImmersion i.left]
  {n m : ℕ} (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m)

local notation "p" => normalBundleProjection i hX hZ
set_option quotPrecheck false in
local notation "a₀" => closedPairOpenInclusion (normalBundleZeroSection i hX hZ).left

set_option Elab.async false in
/-- The original restriction from the chart to the whole supported normal motive. -/
def normalBundleThomRestriction (U : Z.left.Opens) :
    (relativeOpenRestrictionMotive k (p) (a₀)).obj U ⟶
      effectiveMotiveWithSupport.{u, w, w'} k (normalBundleZeroSection i hX hZ) :=
  (relativeOpenRestrictionMotive k (p) (a₀)).map (homOfLE (le_top : U ≤ ⊤)) ≫
    (relativeOpenRestrictionTopIso k (p) (a₀)).hom

/-- The chart restriction is induced by the literal inclusion on the ambient normal bundle. -/
theorem normalBundleThomRestriction_eq_map (U : Z.left.Opens) :
    normalBundleThomRestriction k i hX hZ U =
      (Φ).map (pairArrowOpenInclusion (a₀) ((p).left ⁻¹ᵁ U)) :=
  relativeOpenRestrictionMotive_map_topIso_hom k (p) (a₀) U

end RestrictionMap

section Pair

variable {Z X Z' X' : SmoothSite (Spec (CommRingCat.of k))} {i : Z ⟶ X} {j : Z' ⟶ X'}
  [IsClosedImmersion i.left] [IsClosedImmersion j.left]
  {f : X ⟶ X'} {g : Z ⟶ Z'} (h : IsPullback i.left g.left f.left j.left)

local notation "v" => smoothNormalFibreBaseChange k h

variable [Flat f.left]

local notation "ν" => closedSupportArrowMap (i := normalBundleZeroSectionOfSmooth i)
  (j := normalBundleZeroSectionOfSmooth j) (f := v) (g := g)
  (smoothNormalFibreBaseChange_zero_isPullback k h)

include h in
/-- The original support map on the normal fibre of a flat square. -/
def effectiveNormalFibreSupportMap :
    effectiveMotiveWithSupport.{u, w, w'} k (normalBundleZeroSectionOfSmooth i) ⟶
      effectiveMotiveWithSupport.{u, w, w'} k (normalBundleZeroSectionOfSmooth j) :=
  (effectivePairMotiveFunctor.{u, w, w'} k).map (ν)

variable [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]

variable {n m : ℕ} (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m)
  (hX' : RelativeDimension X'.hom n) (hZ' : RelativeDimension Z'.hom m)

local notation "p" => normalBundleProjection i hX hZ
local notation "p'" => normalBundleProjection j hX' hZ'
set_option quotPrecheck false in
local notation "a₀" => closedPairOpenInclusion (normalBundleZeroSection i hX hZ).left
set_option quotPrecheck false in
local notation "a₁" => closedPairOpenInclusion (normalBundleZeroSection j hX' hZ').left
local notation "F" => conormalSheafDegreeOne i.left
local notation "F'" => conormalSheafDegreeOne j.left

set_option Elab.async false in
set_option maxHeartbeats 1100000 in
-- Preserve the original arrow maps by comparing their ambient components.
/-- A chart with the pulled-back basis has the restricted normalized Thom class. -/
theorem normalBundleBasisThomClass_baseChange (V : Z'.left.affineOpens)
    (hW : IsAffineOpen (g.left ⁻¹ᵁ V.1))
    (b : Module.Basis (Fin (n - m)) Γ(Z'.left, V.1) Γ(F', V.1))
    (b' : Module.Basis (Fin (n - m)) Γ(Z.left, g.left ⁻¹ᵁ V.1) Γ(F, g.left ⁻¹ᵁ V.1))
    (hb : ∀ r, b' r = conormalSectionBaseChange h V.1 (b r)) :
    let W : Z.left.affineOpens := ⟨g.left ⁻¹ᵁ V.1, hW⟩
    let τ := normalBundleThomClass.{u, w, w', w''} k j hX' hZ'
    normalBundleThomRestriction k j hX' hZ' V.1 ≫ τ =
        normalBundleBasisThomClass.{u, w, w', w''} k j hX' hZ' V b →
    normalBundleThomRestriction k i hX hZ W.1 ≫ effectiveNormalFibreSupportMap k h ≫ τ =
        normalBundleBasisThomClass.{u, w, w', w''} k i hX hZ W b' := by
  intro W τ ht
  let P : Arrow Sm ⥤ EffectiveMotivesMinus.{u, w'} k := effectivePairMotiveFunctor.{u, w, w'} k
  let B := (p).left ⁻¹ᵁ W.1
  let C := (p').left ⁻¹ᵁ V.1
  let U := (opensFunctor Z).obj W.1
  let U' := (opensFunctor Z').obj V.1
  let : IsAffine U.left := W.2
  let : IsAffine U'.left := V.2
  let d := preimageOpenMap Z' g V.1
  let e := normalBundleBasisArrowIso k i hX hZ W b'
  let e' := normalBundleBasisArrowIso k j hX' hZ' V b
  let β := closedSupportArrowMap (f := affineSpaceObjectMap d (n - m)) (g := d)
    (affineSpaceOrigin_isPullback d (n - m))
  let α := e.hom ≫ β ≫ e'.inv
  let := smooth_closedPair_comp i
  let := smooth_closedPair_comp j
  let r := (v).left.resLE C B
    (preimage_normalBundleToBase_le_deformationNormalFibreMap h X.hom X'.hom V.1)
  let e₀ := Modules.vectorBundleBasisChart (F) W b'
  let e₁ := Modules.vectorBundleBasisChart (F') V b
  have he₀ : e.hom.right.left = e₀.hom :=
    congrArg (fun t => t.left) (normalBundleBasisArrowIso_hom_right k i hX hZ W b')
  have he₁ : e'.hom.right.left = e₁.hom :=
    congrArg (fun t => t.left) (normalBundleBasisArrowIso_hom_right k j hX' hZ' V b)
  have hr₀ : r ≫ e₁.hom = e₀.hom ≫ β.right.left := by
    change r ≫ e₁.hom =
      e₀.hom ≫ AffineSpace.map (ULift.{u} (Fin (n - m)))
        (g.left.resLE V.1 (g.left ⁻¹ᵁ V.1) le_rfl)
    exact (vectorBundleBasisChart_deformationNormalFibreMap h X.hom X'.hom V hW b b' hb).trans
      (congrArg (fun a => e₀.hom ≫ AffineSpace.map (ULift.{u} (Fin (n - m))) a)
        (Scheme.Hom.resLE_eq_morphismRestrict (U := V.1) g.left).symm)
  have hr : r ≫ (e'.hom.right).left = e.hom.right.left ≫ β.right.left :=
    (congrArg (r ≫ ·) he₁).trans (hr₀.trans (congrArg (· ≫ β.right.left) he₀.symm))
  have hinv : e'.inv.right.left ≫ e'.hom.right.left = 𝟙 _ :=
    congrArg (fun a => a.right.left) e'.inv_hom_id
  have hright : α.right.left = r := by
    let : IsIso e'.hom.right.left := inferInstanceAs
      (IsIso (((Arrow.rightFunc ⋙ forgetScheme S).mapIso e').hom))
    apply (cancel_mono e'.hom.right.left).1
    change (e.hom.right.left ≫ β.right.left ≫ e'.inv.right.left) ≫ e'.hom.right.left = _
    rw [Category.assoc, Category.assoc, hinv, Category.comp_id, hr]
  let s := pairArrowOpenInclusion (a₀) B
  let s' := pairArrowOpenInclusion (a₁) C
  have hs : s ≫ (ν) = α ≫ s' := by
    apply openPairArrowMap_eq_of_right
    apply MorphismProperty.Over.Hom.ext
    change B.ι ≫ (v).left = α.right.left ≫ C.ι
    rw [hright]
    exact (Scheme.Hom.resLE_comp_ι _ _).symm
  let c := effectiveAffineSpaceThomClass k U (n - m)
  let c' := effectiveAffineSpaceThomClass k U' (n - m)
  have hα : α ≫ e'.hom = e.hom ≫ β := by
    simp only [α, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hφ : P.map α ≫ P.map e'.hom = P.map e.hom ≫ P.map β :=
    (P.map_comp _ _).symm.trans ((P.congr_map hα).trans (P.map_comp _ _))
  have hβ : P.map β ≫ c' = c := effectiveAffineSpaceThomClass_naturality k d (n - m)
  have hm : P.map α ≫ normalBundleBasisThomClass k j hX' hZ' V b =
      normalBundleBasisThomClass k i hX hZ W b' := by
    calc
      _ = P.map α ≫ P.map e'.hom ≫ c' :=
        congrArg (P.map α ≫ ·) (normalBundleBasisThomClass_eq_map k j hX' hZ' V b)
      _ = (P.map α ≫ P.map e'.hom) ≫ c' := (Category.assoc _ _ _).symm
      _ = (P.map e.hom ≫ P.map β) ≫ c' := congrArg (· ≫ c') hφ
      _ = P.map e.hom ≫ P.map β ≫ c' := Category.assoc _ _ _
      _ = P.map e.hom ≫ c := congrArg (P.map e.hom ≫ ·) hβ
      _ = _ := (normalBundleBasisThomClass_eq_map k i hX hZ W b').symm
  have hs' : P.map s ≫ P.map (ν) = P.map α ≫ P.map s' :=
    (P.map_comp _ _).symm.trans ((P.congr_map hs).trans (P.map_comp _ _))
  have ht' : P.map s' ≫ τ = normalBundleBasisThomClass k j hX' hZ' V b :=
    (congrArg (· ≫ τ) (normalBundleThomRestriction_eq_map k j hX' hZ' V.1)).symm.trans ht
  calc
    _ = P.map s ≫ P.map (ν) ≫ τ :=
      congrArg (· ≫ P.map (ν) ≫ τ) (normalBundleThomRestriction_eq_map k i hX hZ W.1)
    _ = (P.map s ≫ P.map (ν)) ≫ τ := (Category.assoc _ _ _).symm
    _ = (P.map α ≫ P.map s') ≫ τ := congrArg (· ≫ τ) hs'
    _ = P.map α ≫ P.map s' ≫ τ := Category.assoc _ _ _
    _ = P.map α ≫ normalBundleBasisThomClass k j hX' hZ' V b :=
      congrArg (P.map α ≫ ·) ht'
    _ = _ := hm

end Pair

end AlgebraicGeometry.MotivicHomotopy
