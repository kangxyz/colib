/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.SmoothParameter
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.SupportedGraphDescent
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedMonoidalTransport
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Native
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionParameterMap
import Colib.Algebra.Homology.CochainComplex.SplitFactorization.ArrowMap
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # Derived tensor with the original smooth product pairs -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

private theorem map_composite_of_commSq {C D : Type*} [Category* C] [Category* D]
    (G : C ⥤ D) {X X' Y Y' : C} {W W' : D}
    (u : X ⟶ X') (t : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    (p : G.obj Y ⟶ W) (p' : G.obj Y' ⟶ W') (z : W ⟶ W')
    (ha : u ≫ a' = a ≫ t) (hp : G.map t ≫ p' = p ≫ z) :
    G.map u ≫ G.map a' ≫ p' = (G.map a ≫ p) ≫ z := by
  have hG : G.map u ≫ G.map a' = G.map a ≫ G.map t :=
    (G.map_comp _ _).symm.trans ((G.congr_map ha).trans (G.map_comp _ _))
  exact CochainComplex.SplitFactorization.comp_map_of_commSq (𝟭 D)
    (G.map t) z p p' (G.map u) (G.map a) (G.map a') hp hG

/-- Applying a functor to the first square and adjoining the second gives
naturality of the pointwise composite. -/
theorem map_composite_naturality {S C D : Type*}
    [Category* S] [Category* C] [Category* D]
    (U : S ⥤ C) (G : C ⥤ D) (V : S ⥤ D) (N : S → C)
    (a : ∀ Y, U.obj Y ⟶ N Y) (p : ∀ Y, G.obj (N Y) ⟶ V.obj Y)
    (t : ∀ {Y Y' : S}, (Y ⟶ Y') → (N Y ⟶ N Y'))
    (ha : ∀ {Y Y' : S} (f : Y ⟶ Y'), U.map f ≫ a Y' = a Y ≫ t f)
    (hp : ∀ {Y Y' : S} (f : Y ⟶ Y'), G.map (t f) ≫ p Y' = p Y ≫ V.map f)
    {Y Y' : S} (f : Y ⟶ Y') :
    (U ⋙ G).map f ≫ G.map (a Y') ≫ p Y' =
      (G.map (a Y) ≫ p Y) ≫ V.map f :=
  map_composite_of_commSq G (U.map f) (t f) (a Y) (a Y') (p Y) (p Y') (V.map f) (ha f) (hp f)

variable (k : Type u) [Field k]

local instance productCoverComparisonCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

local instance productCoverComparisonSmoothSheafify :
    HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

local notation "Sm(" K ")" => SmoothSite (Spec (CommRingCat.of K))
local notation "NST" => LargeSheaves k
local notation "s" => singleTransferSheafMinus k
local notation "sₚ" => singleDerivedMinus k 0
local notation "A" => derivedNisnevichSheafification k
set_option quotPrecheck false in
local notation "θ" => Cor.graphFunctorCompTensorRightIso (k := k)
local notation "γ" => Cor.graphFunctor k
local notation "C₀" => curriedTensor (Cor k)
set_option quotPrecheck false in
local notation "d" => derivedConvolutionTensorIso (k := k)
set_option quotPrecheck false in
local notation "R₀" => (γ ⋙ representableLarge k) ⋙ sₚ

/-- The abelian structure on transfer sheaves used by the projective pair augmentation. -/
local instance productCoverComparisonAbelian : Abelian NST := SheafWithTransfers.abelian k

attribute [local instance] derivedConvolutionMonoidalCategory

omit [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)] in
private theorem productParameter_graph_naturality {Y Y' : Sm(k)} (f : Y ⟶ Y') (X : Sm(k)) :
    ((C₀).flip.map ((γ).map f)).app (Cor.mk X) ≫ (θ Y').hom.app X =
      (θ Y).hom.app X ≫ (γ).map ((parameterMap f).app X) := by
  let η := (C₀).flip.map ((γ).map f)
  change η.app (Cor.mk X) ≫ 𝟙 _ = 𝟙 _ ≫ (γ).map (SmoothSite.productMap (𝟙 X) f)
  exact (Category.comp_id _).trans ((Cor.rightExteriorParameterMap_app f (Cor.mk X)).trans
    (Category.id_comp _).symm)

variable {U V : Sm(k)} (j : U ⟶ V) [IsOpenImmersion j.left]

set_option quotPrecheck false in
local notation "P" => (projectivePairDerived k).obj (Arrow.mk j)

/-- The original smooth product pair as a functor of its right factor. -/
def pairProductParameter (j : U ⟶ V) : Sm(k) ⥤ Arrow Sm(k) where
  obj Y := Arrow.mk ((parameterProduct Y).map j)
  map f := smoothParameterArrowMap f (Arrow.mk j)
  map_id Y := by
    apply Arrow.hom_ext
    · exact (smoothCoverLeftProduct U).map_id Y
    · exact (smoothCoverLeftProduct V).map_id Y
  map_comp f g := by
    apply Arrow.hom_ext
    · exact (smoothCoverLeftProduct U).map_comp f g
    · exact (smoothCoverLeftProduct V).map_comp f g

set_option quotPrecheck false in
local notation "Src₀" => R₀ ⋙ tensorLeft P
set_option quotPrecheck false in
local notation "Src" => Src₀ ⋙ A
set_option quotPrecheck false in
local notation "Dst" => pairProductParameter k j ⋙ (transferPairCokernelFunctor k) ⋙ s

set_option quotPrecheck false in
local notation "Dₚ(" Y ")" => derivedParameterPushforward ((C₀).flip.obj (Cor.mk Y))

/-- The transported signed tensor followed by the map into parameter pushforward. -/
def derivedProductPairConvolutionHom (Y : Sm(k)) :
    (tensorLeft P).obj ((R₀).obj Y) ⟶ (Dₚ(Y)).obj P :=
  ((d).app P).hom.app ((R₀).obj Y) ≫ (derivedConvolutionParameterIso C₀ (Cor.mk Y)).hom.app P

/-- The comparison sends the derived tensor to the original quotient augmentation. -/
def derivedProductPairEndHom (Y : Sm(k)) : (Src).obj Y ⟶ (Dst).obj Y :=
  (A).map (derivedProductPairConvolutionHom k j Y) ≫
    projectiveSmoothParameterPairAugmentation (θ Y) (Arrow.mk j)

-- Keep the coefficient constructions at the endpoints selected by their interfaces.
attribute [local irreducible] derivedConvolutionTensorIso derivedConvolutionParameterIso
  projectiveSmoothParameterPairAugmentation

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1250000 in
-- Use the three original isomorphisms to certify the composite map.
/-- The derived product comparison is invertible for an open pair. -/
instance derivedProductPairEndHom_isIso (Y : Sm(k)) : IsIso (derivedProductPairEndHom k j Y) := by
  let e := ((d).app P).app ((R₀).obj Y)
  let a := (derivedConvolutionParameterIso C₀ (Cor.mk Y)).app P
  let p := projectiveSmoothParameterPairAugmentation (θ Y) (Arrow.mk j)
  let t := (A).mapIso (e ≪≫ a)
  have hp : IsIso p := isIso_projectiveSmoothParameterPairAugmentation (θ Y) j
  have ht : t.hom ≫ p = derivedProductPairEndHom k j Y := rfl
  exact ht ▸ IsIso.comp_isIso' t.isIso_hom hp

/-- The derived tensor of the pair with a smooth representable sheafifies to the
degree-zero quotient of the original product pair. -/
@[implicit_reducible]
def derivedProductPairEndIso (Y : Sm(k)) : (Src).obj Y ≅ (Dst).obj Y :=
  asIso (derivedProductPairEndHom k j Y)

/-- The actual map of parameter pushforwards on the projective pair. -/
def derivedProductPairCoefficientMap {Y Y' : Sm(k)} (f : Y ⟶ Y') :
    (Dₚ(Y)).obj P ⟶ (Dₚ(Y')).obj P :=
  (projectiveDerivedMinusFunctorMap
    (coendPushforwardParameterMap ((C₀).flip.map ((γ).map f)))).app P

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 1500000 in
-- Compare the tensorator and the coefficient map before applying sheafification.
omit [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)] [IsOpenImmersion j.left] in
/-- The convolution comparison carries the actual derived map of parameters. -/
theorem derivedProductPairConvolutionHom_naturality {Y Y' : Sm(k)} (f : Y ⟶ Y') :
    (tensorLeft P).map ((R₀).map f) ≫ derivedProductPairConvolutionHom k j Y' =
      derivedProductPairConvolutionHom k j Y ≫ derivedProductPairCoefficientMap k j f := by
  let g : Cor.mk Y ⟶ Cor.mk Y' := (γ).map f
  let X := (sₚ).obj ((representableLarge k).obj (Cor.mk Y))
  let X' := (sₚ).obj ((representableLarge k).obj (Cor.mk Y'))
  let m : X ⟶ X' := (sₚ).map ((representableLarge k).map g)
  let b := (d).app P
  let a := (derivedConvolutionParameterIso C₀ (Cor.mk Y)).hom.app P
  let a' := (derivedConvolutionParameterIso C₀ (Cor.mk Y')).hom.app P
  let u := (tensorLeft P).map m
  let v := ((derivedConvolution C₀).obj P).map m
  let t := (projectiveDerivedMinusFunctorMap (coendPushforwardParameterMap ((C₀).flip.map g))).app P
  let b₀ := b.hom.app X
  let b₁ := b.hom.app X'
  have h₁ : CommSq b₀ u v b₁ := ⟨(b.hom.naturality m).symm⟩
  have h₂ : CommSq a v t a' :=
    ⟨(derivedConvolutionParameterIso_naturality_right C₀
      (T := Cor.mk Y) (T' := Cor.mk Y') g P).symm⟩
  have hleft : (tensorLeft P).map ((R₀).map f) ≫ derivedProductPairConvolutionHom k j Y' =
      u ≫ (b₁ ≫ a') := rfl
  have hright : derivedProductPairConvolutionHom k j Y ≫ derivedProductPairCoefficientMap k j f =
      (b₀ ≫ a) ≫ t := rfl
  exact hleft.trans ((h₁.horiz_comp h₂).w.symm.trans hright.symm)

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 2500000 in
-- Apply the original augmentation square at the literal parameter arrow map.
omit [IsOpenImmersion j.left] in
/-- The augmentation commutes with the map of the corresponding smooth product pairs. -/
theorem derivedProductPairAugmentation_naturality {Y Y' : Sm(k)} (f : Y ⟶ Y') :
    (A).map (derivedProductPairCoefficientMap k j f) ≫
        projectiveSmoothParameterPairAugmentation (θ Y') (Arrow.mk j) =
      projectiveSmoothParameterPairAugmentation (θ Y) (Arrow.mk j) ≫
        (s).map ((transferPairCokernelFunctor k).map (smoothParameterArrowMap f (Arrow.mk j))) := by
  let g : Cor.mk Y ⟶ Cor.mk Y' := (γ).map f
  let η := (C₀).flip.map g
  let t := (projectiveDerivedMinusFunctorMap (coendPushforwardParameterMap η)).app P
  let p := projectiveSmoothParameterPairAugmentation (θ Y) (Arrow.mk j)
  let p' := projectiveSmoothParameterPairAugmentation (θ Y') (Arrow.mk j)
  let q := (s).map ((transferPairCokernelFunctor k).map (smoothParameterArrowMap f (Arrow.mk j)))
  have ht : derivedProductPairCoefficientMap k j f = t := rfl
  have hp : (A).map t ≫ p' = p ≫ q :=
    projectiveSmoothParameterPairAugmentation_parameter (k := k) (T := Y) (T' := Y')
      (F := (C₀).flip.obj (Cor.mk Y)) (F' := (C₀).flip.obj (Cor.mk Y'))
      (θ Y) (θ Y') f η (productParameter_graph_naturality k f) (Arrow.mk j)
  exact (congrArg (fun a => (A).map a ≫ p') ht).trans hp

end AlgebraicGeometry.MotivicHomotopy
