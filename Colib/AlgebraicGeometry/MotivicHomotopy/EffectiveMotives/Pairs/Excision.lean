/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Comparison
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.TransferTriangle
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.TransferExcision
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-!
# Nisnevich excision and Mayer–Vietoris for effective motives

The original transfer quotient excision becomes an isomorphism on relative
effective motives. The signed transfer sequence gives the Mayer–Vietoris
triangle with the original smooth motive maps.
-/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

attribute [local irreducible] Cor.graphFunctor transferRepresentable

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))
local notation "NST(" field ")" => LargeSheaves field
local notation "R" => smoothTransferRepresentable k

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} NST(k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "F" => effectiveTransferSheaf k
local notation "G" => effectiveSmoothMotive k
local notation "e" => smoothTransferRepresentableEffectiveIso k

section AdditiveTransport

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Preadditive D] [Preadditive E] [HasBinaryBiproducts D] [HasBinaryBiproducts E]
  [HasShift E ℤ] (J : C ⥤ D) (L : D ⥤ E) [L.Additive] [PreservesBinaryBiproducts L]
  (K : C ⥤ E) (ε : J ⋙ L ≅ K) (s : Square C)

private def mayerVietorisBiprodIso :
    L.obj (J.obj s.X₂ ⊞ J.obj s.X₃) ≅ K.obj s.X₂ ⊞ K.obj s.X₃ :=
  L.mapBiprod _ _ ≪≫ biprod.mapIso (ε.app s.X₂) (ε.app s.X₃)

private def mayerVietorisTriangleIso
    (δ : L.obj (J.obj s.X₄) ⟶ (L.obj (J.obj s.X₁))⟦(1 : ℤ)⟧) :
    Triangle.mk (L.map (biprod.lift (J.map s.f₁₂) (-(J.map s.f₁₃))))
        (L.map (biprod.desc (J.map s.f₂₄) (J.map s.f₃₄))) δ ≅
      Triangle.mk (biprod.lift (K.map s.f₁₂) (-(K.map s.f₁₃)))
        (biprod.desc (K.map s.f₂₄) (K.map s.f₃₄))
        ((ε.app s.X₄).inv ≫ δ ≫ (ε.app s.X₁).hom⟦(1 : ℤ)⟧') := by
  refine Triangle.isoMk _ _ (ε.app s.X₁) (mayerVietorisBiprodIso J L K ε s)
    (ε.app s.X₄) ?_ ?_ ?_
  · change L.map (biprod.lift (J.map s.f₁₂) (-(J.map s.f₁₃))) ≫
        (L.mapBiprod _ _).hom ≫ biprod.map (ε.app s.X₂).hom (ε.app s.X₃).hom =
      (ε.app s.X₁).hom ≫ biprod.lift (K.map s.f₁₂) (-(K.map s.f₁₃))
    rw [← Category.assoc, biprod.map_lift_mapBiprod, L.map_neg]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst, biprod.lift_fst_assoc]
      exact ε.hom.naturality s.f₁₂
    · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd, biprod.lift_snd_assoc,
        Preadditive.neg_comp, Preadditive.comp_neg]
      exact congrArg Neg.neg (ε.hom.naturality s.f₁₃)
  · change L.map (biprod.desc (J.map s.f₂₄) (J.map s.f₃₄)) ≫ (ε.app s.X₄).hom =
      ((L.mapBiprod _ _).hom ≫ biprod.map (ε.app s.X₂).hom (ε.app s.X₃).hom) ≫
        biprod.desc (K.map s.f₂₄) (K.map s.f₃₄)
    rw [← biprod.mapBiprod_hom_desc L, Category.assoc, Category.assoc]
    congr 1
    apply biprod.hom_ext'
    · simp only [biprod.inl_desc, biprod.inl_desc_assoc, biprod.inl_map_assoc]
      exact ε.hom.naturality s.f₂₄
    · simp only [biprod.inr_desc, biprod.inr_desc_assoc, biprod.inr_map_assoc]
      exact ε.hom.naturality s.f₃₄
  · change δ ≫ (ε.app s.X₁).hom⟦(1 : ℤ)⟧' =
      (ε.app s.X₄).hom ≫ (ε.app s.X₄).inv ≫ δ ≫ (ε.app s.X₁).hom⟦(1 : ℤ)⟧'
    exact (Iso.hom_inv_id_assoc _ _).symm

end AdditiveTransport

/-- Use the native transfer abelian structure for the exact Mayer–Vietoris triangle. -/
local instance instAbelianEffectiveExcision : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

local instance instEffectiveTransferSheafPreservesBinaryBiproducts :
    PreservesBinaryBiproducts (F) :=
  preservesBinaryBiproducts_of_preservesBiproducts (F)

variable (sq : Square Sm(k))

/-- Transport the original signed sequence of transfer representables to smooth motives. -/
@[expose] def effectiveMayerVietorisTriangleOfPushout
    (h : (transferMayerVietorisSequence k sq).ShortExact) :
    Triangle (EffectiveMotivesMinus k) :=
  Triangle.mk (biprod.lift ((G).map sq.f₁₂) (-((G).map sq.f₁₃)))
    (biprod.desc ((G).map sq.f₂₄) ((G).map sq.f₃₄))
    (((e).app sq.X₄).inv ≫ (effectiveTransferSheafTriangle k h).mor₃ ≫
      ((e).app sq.X₁).hom⟦(1 : ℤ)⟧')

/-- The ordinary smooth Mayer–Vietoris triangle uses the original transfer connecting map. -/
def effectiveMayerVietorisTriangleOfPushoutIso
    (h : (transferMayerVietorisSequence k sq).ShortExact) :
    effectiveTransferSheafTriangle k h ≅ effectiveMayerVietorisTriangleOfPushout k sq h :=
  mayerVietorisTriangleIso (R) (F) (G) (e) sq (effectiveTransferSheafTriangle k h).mor₃

/-- The ordinary cover comparison on the intersection is the represented motive map. -/
@[simp]
theorem effectiveMayerVietorisTriangleOfPushoutIso_hom₁
    (h : (transferMayerVietorisSequence k sq).ShortExact) :
    (effectiveMayerVietorisTriangleOfPushoutIso k sq h).hom.hom₁ = (e).hom.app sq.X₁ := by
  unfold effectiveMayerVietorisTriangleOfPushoutIso mayerVietorisTriangleIso
  rfl

/-- The ordinary cover comparison on the two charts is the biproduct comparison. -/
@[simp]
theorem effectiveMayerVietorisTriangleOfPushoutIso_hom₂
    (h : (transferMayerVietorisSequence k sq).ShortExact) :
    (effectiveMayerVietorisTriangleOfPushoutIso k sq h).hom.hom₂ =
      ((F).mapBiprod ((R).obj sq.X₂) ((R).obj sq.X₃)).hom ≫
        biprod.map ((e).hom.app sq.X₂) ((e).hom.app sq.X₃) := by
  unfold effectiveMayerVietorisTriangleOfPushoutIso mayerVietorisTriangleIso mayerVietorisBiprodIso
  rfl

/-- The ordinary cover comparison on the union is the represented motive map. -/
@[simp]
theorem effectiveMayerVietorisTriangleOfPushoutIso_hom₃
    (h : (transferMayerVietorisSequence k sq).ShortExact) :
    (effectiveMayerVietorisTriangleOfPushoutIso k sq h).hom.hom₃ = (e).hom.app sq.X₄ := by
  unfold effectiveMayerVietorisTriangleOfPushoutIso mayerVietorisTriangleIso
  rfl

private theorem effectiveMayerVietorisTriangleOfPushout_distinguished
    (h : (transferMayerVietorisSequence k sq).ShortExact) :
    effectiveMayerVietorisTriangleOfPushout k sq h ∈ distTriang _ := by
  exact isomorphic_distinguished _ (effectiveTransferSheafTriangle_distinguished k h) _
    (effectiveMayerVietorisTriangleOfPushoutIso k sq h).symm

section Nisnevich

variable (hpb : sq.IsPullback) [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
  {Z : Scheme.{u}} (z : Z ⟶ sq.X₄.left) [IsClosedImmersion z]
  (hcomp : Set.range z = (Set.range sq.f₂₄.left)ᶜ) [IsIso (pullback.snd sq.f₃₄.left z)]

/-- Mayer–Vietoris for a Nisnevich distinguished square of smooth schemes.
The maps on the first two sides are the difference and sum of the actual motive maps. -/
@[expose] def effectiveMotiveMayerVietorisTriangle : Triangle (EffectiveMotivesMinus k) :=
  effectiveMayerVietorisTriangleOfPushout k sq
    (transferMayerVietorisSequence_shortExact k sq hpb (transferSquare_isPushout k sq hpb z hcomp))

/-- The Mayer–Vietoris triangle of a Nisnevich distinguished square is distinguished. -/
theorem effectiveMotiveMayerVietorisTriangle_distinguished :
    effectiveMotiveMayerVietorisTriangle k sq hpb z hcomp ∈ distTriang _ :=
  effectiveMayerVietorisTriangleOfPushout_distinguished k sq _

end Nisnevich

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem isIso_map_coker_mapArrow_of_isPushout {C D E : Type*}
    [Category C] [Category D] [Category E] [HasZeroMorphisms D] [HasCokernels D]
    (J : C ⥤ D) (L : D ⥤ E) (s : Square C) (h : (s.map J).IsPushout) :
    IsIso (L.map ((J.mapArrow ⋙ coker D).map (Arrow.homMk' s.f₁₂ s.f₃₄ s.fac))) := by
  let f := J.map s.f₁₃
  let g := J.map s.f₁₂
  let p := J.map s.f₃₄
  let q := J.map s.f₂₄
  have hp : IsPushout f g p q := h.flip
  let m : cokernel f ⟶ cokernel q := cokernel.map f q g p hp.w
  let : IsIso m := isIso_cokernel_map_of_isPushout hp
  exact L.map_isIso m

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The actual support-excision map is the isomorphism between the
cofibers of the two vertical open immersions in the distinguished square. -/
theorem effectivePairMotiveMap_isIso (hpb : sq.IsPullback)
    [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
    {Z : Scheme.{u}} (z : Z ⟶ sq.X₄.left) [IsClosedImmersion z]
    (hcomp : Set.range z = (Set.range sq.f₂₄.left)ᶜ)
    [IsIso (pullback.snd sq.f₃₄.left z)] :
    IsIso (effectivePairMotiveMap k sq) := by
  let J : Sm(k) ⥤ NST(k) := smoothTransferRepresentable k
  let L : NST(k) ⥤ EffectiveMotivesMinus k := effectiveTransferSheaf k
  have h : (sq.map J).IsPushout := transferSquare_isPushout k sq hpb z hcomp
  change IsIso (L.map ((J.mapArrow ⋙ coker NST(k)).map
    (Arrow.homMk' sq.f₁₂ sq.f₃₄ sq.fac)))
  exact isIso_map_coker_mapArrow_of_isPushout J L sq h

section OpenCover

variable (hpb : sq.IsPullback) [IsOpenImmersion sq.f₂₄.left] [IsOpenImmersion sq.f₃₄.left]
  (hcover : Set.range sq.f₂₄.left ∪ Set.range sq.f₃₄.left = Set.univ)

/-- The original signed Mayer–Vietoris triangle for two open covering charts. -/
@[expose] def effectiveMotiveOpenCoverTriangle : Triangle (EffectiveMotivesMinus k) :=
  effectiveMayerVietorisTriangleOfPushout k sq
    (transferMayerVietorisSequence_shortExact k sq hpb
      (transferSquare_isPushout_of_openCover k sq hpb hcover))

/-- The original two-chart Mayer–Vietoris triangle is distinguished. -/
theorem effectiveMotiveOpenCoverTriangle_distinguished :
    effectiveMotiveOpenCoverTriangle k sq hpb hcover ∈ distTriang _ :=
  effectiveMayerVietorisTriangleOfPushout_distinguished k sq _

end OpenCover

end AlgebraicGeometry.MotivicHomotopy
