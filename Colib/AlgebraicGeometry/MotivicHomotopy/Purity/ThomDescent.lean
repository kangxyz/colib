/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ThomGraphBasic
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.SupportedProductCover
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Excision
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.NormalBundleChartCover
import Colib.AlgebraicGeometry.Correspondences.Coproducts.Zero
import Colib.Algebra.Homology.DerivedCategory.MapTriangleCommShift
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # Invertibility of the supported Thom map by open-cover descent -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme SmoothSite Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

private theorem biprod_map_comp_comparison {C D : Type*} [Category* C] [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F G : C ⥤ D) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [PreservesBinaryBiproducts F] [PreservesBinaryBiproducts G] (c : F ⟶ G)
    {X₂ X₃ : C} {A₂ A₃ B₂ B₃ : D} (a₂ : A₂ ⟶ B₂) (a₃ : A₃ ⟶ B₃)
    (e₂ : F.obj X₂ ≅ B₂) (e₃ : F.obj X₃ ≅ B₃) :
    (biprod.map a₂ a₃ ≫ (F.mapBiprod X₂ X₃ ≪≫ biprod.mapIso e₂ e₃).inv ≫
        c.app (X₂ ⊞ X₃)) ≫ (G.mapBiprod X₂ X₃).hom =
      biprod.map (a₂ ≫ e₂.inv ≫ c.app X₂) (a₃ ≫ e₃.inv ≫ c.app X₃) := by
  have h : c.app (X₂ ⊞ X₃) ≫ (G.mapBiprod X₂ X₃).hom =
      (F.mapBiprod X₂ X₃).hom ≫ biprod.map (c.app X₂) (c.app X₃) := by
    apply biprod.hom_ext
    · simpa only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst,
        biprod.lift_fst_assoc, biprod.map_fst] using
        (c.naturality (biprod.fst : X₂ ⊞ X₃ ⟶ X₂)).symm
    · simpa only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_snd,
        biprod.lift_snd_assoc, biprod.map_snd] using
        (c.naturality (biprod.snd : X₂ ⊞ X₃ ⟶ X₃)).symm
  simp only [Category.assoc, h, Iso.trans_inv, biprod.mapIso_inv, Iso.inv_hom_id_assoc]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprod.map_fst_assoc]
  · simp only [Category.assoc, biprod.map_snd, biprod.map_snd_assoc]

private theorem isIso_triangle_comp_hom₃ {C : Type*} [Category* C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {S P T U : Triangle C} (s : S ⟶ P) (e : T ≅ P) (c : T ⟶ U)
    (hs : S ∈ distTriang C) (hu : U ∈ distTriang C)
    {B : C} (d : U.obj₂ ≅ B) (b : S.obj₂ ≅ B)
    (h₁ : IsIso (s.hom₁ ≫ e.inv.hom₁ ≫ c.hom₁))
    (h₂ : (s.hom₂ ≫ e.inv.hom₂ ≫ c.hom₂) ≫ d.hom = b.hom) :
    IsIso (s.hom₃ ≫ e.inv.hom₃ ≫ c.hom₃) :=
  isIso₃_of_isIso₁₂ (s ≫ e.inv ≫ c) hs hu h₁ (IsIso.of_isIso_fac_right h₂)

variable (k : Type u) [Field k] [PerfectField k]

/-- The canonical additive sheafification on the Nisnevich correspondence site. -/
local instance thomDescentCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

/-- The canonical additive sheafification on the smooth Nisnevich site. -/
local instance thomDescentSmoothSheafify :
    HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Sm(" K ")" => SmoothSite (Spec (CommRingCat.of K))
local notation "E(" K ")" => EffectiveMotivesMinus K
local notation "M" => effectiveSmoothMotive k
set_option quotPrecheck false in
local notation "θ" => Cor.graphFunctorCompTensorRightIso (k := k)

/-- The canonical abelian structure on sheaves with transfers. -/
local instance thomDescentAbelian : Abelian (SheafWithTransfers.{u + 1} k) :=
  SheafWithTransfers.abelian k

/-- Signed convolution on effective motives. -/
local instance thomDescentMonoidal : MonoidalCategory E(k) :=
  effectiveSignedConvolutionMonoidalCategory θ

/-- The two shift structures of the signed convolution tensor. -/
local instance thomDescentCommShift₂Int : (curriedTensor E(k)).CommShift₂Int :=
  effectiveSignedConvolutionCommShift₂Int θ

/-- Signed convolution is additive in each tensor variable. -/
local instance thomDescentMonoidalPreadditive : MonoidalPreadditive E(k) :=
  effectiveSignedConvolutionMonoidalPreadditive θ

/-- Left tensor preserves the binary biproduct of the two chart motives. -/
local instance thomDescentPreservesBinaryBiproducts (K : E(k)) :
    PreservesBinaryBiproducts (tensorLeft K) :=
  preservesBinaryBiproducts_of_preservesBiproducts (tensorLeft K)

omit [HasDerivedCategory AddCommGrpCat.{u + 1}] in
private theorem isZero_effectiveSmoothMotive_of_isEmpty (Y : Sm(k)) [IsEmpty Y.left] :
    IsZero ((M).obj Y) := by
  let A := Cor.mk Y
  have h : IsZero A :=
    (IsZero.iff_id_eq_zero _).2 (Cor.hom_eq_zero_of_isEmpty_source k (𝟙 A))
  let R := SheafWithTransfers.transferRepresentable k
  let F := effectiveTransferSheaf k
  have hR : IsZero (F.obj (R.obj A)) := F.map_isZero (R.map_isZero h)
  exact ((smoothTransferRepresentableEffectiveIso k).app Y).isZero_iff.mp hR

section OpenCover

variable {A V Z : Sm(k)} (p : V ⟶ Z) (j : A ⟶ V) [IsOpenImmersion j.left]
  {K : E(k)} (t : effectivePairMotive k j ⟶ K)

local notation "Thom(" W ")" => effectiveRestrictedThomGraph k p j W t

private theorem isIso_Thom_bot : IsIso (Thom(⊥)) := by
  let Y := (opensFunctor Z).obj (⊥ : Z.left.Opens)
  let : IsEmpty Y.left := ⟨fun x => x.property⟩
  have h₀ := isZero_relativeOpenRestrictionMotive_bot k p j
  have h₁ := (tensorLeft K).map_isZero (isZero_effectiveSmoothMotive_of_isEmpty k Y)
  let e := h₀.iso h₁
  exact (h₀.eq_of_src (Thom(⊥)) e.hom).symm ▸ e.isIso_hom

section BinaryCover

attribute [local irreducible] Cor.graphFunctor SheafWithTransfers.transferRepresentable

set_option maxHeartbeats 1800000 in
-- The original graph identifies the endpoints of the two signed cover triangles.
private theorem isIso_Thom_sup (W W' : Z.left.Opens)
    (hW : IsIso (Thom(W))) (hW' : IsIso (Thom(W')))
    (hI : IsIso (Thom(W ⊓ W'))) : IsIso (Thom(W ⊔ W')) := by
  let sq := openUnionCoverSquare Z W W'
  let sb := openUnionCoverSquare V (p.left ⁻¹ᵁ W) (p.left ⁻¹ᵁ W')
  let sa := openUnionCoverSquare A (j.left ⁻¹ᵁ (p.left ⁻¹ᵁ W)) (j.left ⁻¹ᵁ (p.left ⁻¹ᵁ W'))
  let a : sa ⟶ sb := preimageOpenUnionCoverMap V (p.left ⁻¹ᵁ W) (p.left ⁻¹ᵁ W') j
  let hsq := openUnionCoverSquare_isPullback Z W W'
  let hcover := openUnionCoverSquare_range_cover Z W W'
  let : IsOpenImmersion sq.f₂₄.left :=
    inferInstanceAs (IsOpenImmersion (openUnionCoverSquare Z W W').f₂₄.left)
  let : IsOpenImmersion sq.f₃₄.left :=
    inferInstanceAs (IsOpenImmersion (openUnionCoverSquare Z W W').f₃₄.left)
  let h := transferMayerVietorisSequence_shortExact k sq hsq
    (transferSquare_isPushout_of_openCover k sq hsq hcover)
  let : IsOpenImmersion a.τ₁.left := inferInstanceAs
    (IsOpenImmersion (preimageOpenMap V j (p.left ⁻¹ᵁ W ⊓ p.left ⁻¹ᵁ W')).left)
  let : IsOpenImmersion a.τ₂.left := inferInstanceAs
    (IsOpenImmersion (preimageOpenMap V j (p.left ⁻¹ᵁ W)).left)
  let : IsOpenImmersion a.τ₃.left := inferInstanceAs
    (IsOpenImmersion (preimageOpenMap V j (p.left ⁻¹ᵁ W')).left)
  let : IsOpenImmersion a.τ₄.left := inferInstanceAs
    (IsOpenImmersion (preimageOpenMap V j (p.left ⁻¹ᵁ W ⊔ p.left ⁻¹ᵁ W')).left)
  let ha : (transferPairOpenCoverSequence k a).ShortExact :=
    relativeOpenRestrictionCover_shortExact k p j W W'
  let hb := transferPairProductOpenCoverSequence_shortExact k j sq hsq hcover
  let ac := openRestrictionComplementProductGraphCoverMap p j W W'
  let bc := openRestrictionProductGraphCoverMap p W W'
  let hc := openRestrictionProductGraphCoverMap_pair_comm p j W W'
  let F := tensorLeft (effectivePairMotive k j)
  let G := tensorLeft K
  let T := effectiveMayerVietorisTriangleOfPushout k sq h
  let X₂ := (M).obj sq.X₂
  let X₃ := (M).obj sq.X₃
  let c : F ⟶ G := (curriedTensor E(k)).map t
  let : NatTrans.CommShift c ℤ := inferInstanceAs
    (NatTrans.CommShift ((curriedTensor E(k)).map t) ℤ)
  let s := effectivePairOpenCoverTriangleMap k ac bc hc ha hb
  let e := effectivePairProductOpenCoverTriangleIso k j sq h hb
  let cT := NatTrans.mapTriangleHom c T
  let a₁ := (effectivePairMotiveFunctor k).map (openRestrictionProductGraphArrowMap p j (W ⊓ W'))
  let a₂ := (effectivePairMotiveFunctor k).map (openRestrictionProductGraphArrowMap p j W)
  let a₃ := (effectivePairMotiveFunctor k).map (openRestrictionProductGraphArrowMap p j W')
  let a₄ := (effectivePairMotiveFunctor k).map (openRestrictionProductGraphArrowMap p j (W ⊔ W'))
  let b₁ := effectivePairProductRightIso k j sq.X₁
  let b₂ := effectivePairProductRightIso k j sq.X₂
  let b₃ := effectivePairProductRightIso k j sq.X₃
  let b₄ := effectivePairProductRightIso k j sq.X₄
  have hs₁ : s.hom₁ = a₁ := effectivePairOpenCoverTriangleMap_hom₁ k ac bc hc ha hb
  have hs₂ : s.hom₂ = biprod.map a₂ a₃ :=
    effectivePairOpenCoverTriangleMap_hom₂ k ac bc hc ha hb
  have hs₃ : s.hom₃ = a₄ := effectivePairOpenCoverTriangleMap_hom₃ k ac bc hc ha hb
  let : IsIso (Thom(W)) := hW
  let : IsIso (Thom(W')) := hW'
  have hf₁ : s.hom₁ ≫ e.inv.hom₁ ≫ cT.hom₁ = Thom(W ⊓ W') := by
    have hv : e.hom.hom₁ = b₁.hom := effectivePairProductOpenCoverTriangleIso_hom₁ k j sq h hb
    have he : Triangle.π₁.mapIso e = b₁ := Iso.ext hv
    have hv' : e.inv.hom₁ = b₁.inv := congrArg Iso.inv he
    change s.hom₁ ≫ e.inv.hom₁ ≫ c.app ((M).obj sq.X₁) =
      a₁ ≫ b₁.inv ≫ c.app ((M).obj sq.X₁)
    exact congrArg₂ (fun u v => u ≫ v ≫ c.app ((M).obj sq.X₁)) hs₁ hv'
  have hf₃ : s.hom₃ ≫ e.inv.hom₃ ≫ cT.hom₃ = Thom(W ⊔ W') := by
    have hv : e.hom.hom₃ = b₄.hom := effectivePairProductOpenCoverTriangleIso_hom₃ k j sq h hb
    have he : Triangle.π₃.mapIso e = b₄ := Iso.ext hv
    have hv' : e.inv.hom₃ = b₄.inv := congrArg Iso.inv he
    change s.hom₃ ≫ e.inv.hom₃ ≫ c.app ((M).obj sq.X₄) =
      a₄ ≫ b₄.inv ≫ c.app ((M).obj sq.X₄)
    exact congrArg₂ (fun u v => u ≫ v ≫ c.app ((M).obj sq.X₄)) hs₃ hv'
  let d := G.mapBiprod X₂ X₃
  let b := biprod.mapIso (asIso (Thom(W))) (asIso (Thom(W')))
  have hh : (s.hom₂ ≫ e.inv.hom₂ ≫ cT.hom₂) ≫ d.hom = b.hom := by
    let e₂ := effectivePairProductOpenCoverMiddleIso k j sq h hb
    have hv : e.hom.hom₂ = e₂.hom := effectivePairProductOpenCoverTriangleIso_hom₂ k j sq h hb
    have he : Triangle.π₂.mapIso e = e₂ := Iso.ext hv
    have hv' : e.inv.hom₂ = e₂.inv := congrArg Iso.inv he
    have hs : (s.hom₂ ≫ e.inv.hom₂ ≫ cT.hom₂) ≫ d.hom =
        (biprod.map a₂ a₃ ≫ e₂.inv ≫ c.app (X₂ ⊞ X₃)) ≫ d.hom := by
      exact congrArg₂ (fun u v => (u ≫ v ≫ c.app (X₂ ⊞ X₃)) ≫ d.hom) hs₂ hv'
    exact hs.trans (biprod_map_comp_comparison F G c a₂ a₃ b₂ b₃)
  let : G.IsTriangulated := effectiveSignedTensorLeft_isTriangulated θ K
  have hdist : T ∈ distTriang E(k) :=
    effectiveMotiveOpenCoverTriangle_distinguished k sq hsq hcover
  exact (congrArg IsIso hf₃).mp
    (isIso_triangle_comp_hom₃ s e cT (effectivePairOpenCoverTriangle_distinguished k ha)
      (G.map_distinguished _ hdist) d b ((congrArg IsIso hf₁).mpr hI) hh)

end BinaryCover

set_option maxHeartbeats 800000 in
-- Keep the restricted graph fixed while applying the finite union induction.
/-- A supported Thom comparison is invertible if every affine subopen of a chosen
finite affine cover has the specified local comparison. -/
theorem isIso_effectiveRestrictedThomGraph_of_cover {I : Type*}
    (s : Finset I) (W : I → Z.left.affineOpens) (hW : s.sup (fun x => (W x).1) = ⊤)
    (hloc : ∀ x ∈ s, ∀ U : Z.left.affineOpens, U.1 ≤ (W x).1 → IsIso (Thom(U.1))) :
    IsIso (Thom(⊤)) := by
  let Q (U : Z.left.Opens) := IsAffineOpen U
  have h := predicate_of_finset_sup_of_inf_closed (fun U => IsIso (Thom(U))) Q
    (isIso_Thom_bot k p j t) (isIso_Thom_sup k p j t)
    (fun U U' hU hU' => isAffineOpen_smooth_intersection k ⟨U, hU⟩ ⟨U', hU'⟩)
    s (fun x => (W x).1) (fun x _ => (W x).2)
    (fun x hx U hU hA => hloc x hx ⟨U, hA⟩ hU)
  exact (congrArg (fun U : Z.left.Opens => IsIso (Thom(U))) hW).mp h

end OpenCover

end AlgebraicGeometry.MotivicHomotopy
