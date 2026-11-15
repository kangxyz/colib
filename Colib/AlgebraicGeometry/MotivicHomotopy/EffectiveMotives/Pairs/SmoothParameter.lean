/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.SmoothParameterCochain
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.ParameterMap
import Colib.Algebra.Homology.CochainComplex.SplitFactorization.ArrowMap
import Colib.AlgebraicGeometry.Sites.Smooth.AffineLine.CylinderRestriction

/-!
# The actual smooth parameter on a relative pair

The effective parameter functor computes on the two projective
representables of the pair. Their images are the actual product
representables, so the specified augmentation gives their relative motive.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable {k : Type u} [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S
local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k

/-- The canonical abelian structure on sheaves with transfers. -/
local instance smoothParameterAbelian : Abelian NST := SheafWithTransfers.abelian k
set_option quotPrecheck false in
local notation "a" => nisnevichSheafify k
local notation "c" => ComplexShape.up ℤ
set_option quotPrecheck false in
local notation "s" => CochainComplex.singleFunctor NST 0

variable {T : SmoothSite (Spec (CommRingCat.of k))} {F : Cor k ⥤ Cor k} [F.Additive]
  (e : Cor.graphFunctor k ⋙ F ≅ parameterProduct T ⋙ Cor.graphFunctor k)

set_option quotPrecheck false in
local notation "H" => coendPushforward F
set_option quotPrecheck false in
local notation "J" => (H ⋙ a)
set_option quotPrecheck false in
local notation "G" => parameterProduct T

variable [HasDerivedCategory.{w} (LargePresheaves k)] [HasDerivedCategory.{w'} (LargeSheaves k)]

set_option quotPrecheck false in
local notation "Q" => (DerivedCategory.Q : CochainComplex NST ℤ ⥤ DerivedCategory NST)

/-- The projective product of a pair augments to the actual transfer quotient
of the product pair. This map is defined for every arrow. -/
def projectiveSmoothParameterPairAugmentation (j : Arrow Sm) :
    (derivedParameterPushforward F ⋙ derivedNisnevichSheafification k).obj
        ((projectivePairDerived k).obj j) ⟶
      (singleTransferSheafMinus k).obj ((transferPairCokernelFunctor k).obj ((G).mapArrow.obj j)) :=
  ObjectProperty.homMk ((projectivePairTermwiseModelIso k H j).hom ≫
    (Q).map (smoothParameterCochainAugmentation e j))

set_option maxHeartbeats 950000 in
-- The quotient map for the original product of an open pair is a quasi-isomorphism.
instance isIso_projectiveSmoothParameterPairAugmentation {U X : Sm} (j : U ⟶ X)
    [IsOpenImmersion j.left] :
    IsIso (projectiveSmoothParameterPairAugmentation e (Arrow.mk j)) := by
  let S₀ := cochainTransferPair k ((G).mapArrow.obj (Arrow.mk j))
  let f := CochainComplex.mappingCone.descShortComplex S₀
  let : IsOpenImmersion ((G).map j).left := parameterProduct_map_isOpenImmersion T j
  have hS : S₀.ShortExact := (transferPairSequence_shortExact k ((G).map j)).map_of_exact (s)
  have hf : QuasiIso f := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  let : IsIso ((Q).map f) := (DerivedCategory.isIso_Q_map_iff_quasiIso NST f).2 hf
  let I : DerivedCategory.Minus NST ⥤ DerivedCategory NST := DerivedCategory.Minus.ι
  let b := projectiveSmoothParameterPairAugmentation e (Arrow.mk j)
  let d := projectivePairTermwiseModelIso k H (Arrow.mk j)
  let v := smoothParameterCochainComparison e (Arrow.mk j)
  have hb : I.map b = d.hom ≫ (Q).map (v.hom ≫ f) := rfl
  have : IsIso (I.map b) := by
    rw [hb, (Q).map_comp]
    infer_instance
  exact isIso_of_reflects_iso b I

set_option maxHeartbeats 1200000 in
-- The comparison retains the original projective and effective pair maps.
/-- The augmentation commutes with the actual maps of pairs. -/
theorem projectiveSmoothParameterPairAugmentation_naturality {i j : Arrow Sm} (φ : i ⟶ j) :
    (derivedParameterPushforward F ⋙ derivedNisnevichSheafification k).map
        ((projectivePairDerived k).map φ) ≫ projectiveSmoothParameterPairAugmentation e j =
      projectiveSmoothParameterPairAugmentation e i ≫
        (singleTransferSheafMinus k).map
          ((transferPairCokernelFunctor k).map ((G).mapArrow.map φ)) := by
  apply ObjectProperty.hom_ext
  let d (x : Arrow Sm) := projectivePairTermwiseModelIso k H x
  let b (x : Arrow Sm) := smoothParameterCochainComparison e x
  let p (x : Arrow Sm) := CochainComplex.mappingCone.descShortComplex
    (cochainTransferPair k ((G).mapArrow.obj x))
  let f := ((J).mapHomologicalComplex c).map ((projectivePairCochain k).map φ)
  let v := cochainTransferPairConeMap k ((G).mapArrow.map φ)
  let g := (s).map ((transferPairCokernelFunctor k).map ((G).mapArrow.map φ))
  let A := derivedParameterPushforward F ⋙ derivedNisnevichSheafification k
  let u := (A.map ((projectivePairDerived k).map φ)).hom
  have h₁ : u ≫ (d j).hom = (d i).hom ≫ (Q).map f :=
    projectivePairTermwiseModelIso_naturality k H φ
  have h₂ : f ≫ (b j).hom = (b i).hom ≫ v :=
    smoothParameterCochainComparison_naturality e φ
  have h₃ : v ≫ p j = p i ≫ g := cochainTransferPairConeMap_desc k ((G).mapArrow.map φ)
  have h₄ : f ≫ ((b j).hom ≫ p j) = ((b i).hom ≫ p i) ≫ g := by
    calc
      _ = (f ≫ (b j).hom) ≫ p j := (Category.assoc _ _ _).symm
      _ = ((b i).hom ≫ v) ≫ p j := congrArg (· ≫ p j) h₂
      _ = (b i).hom ≫ (p i ≫ g) :=
        (Category.assoc _ _ _).trans (congrArg ((b i).hom ≫ ·) h₃)
      _ = _ := (Category.assoc _ _ _).symm
  exact CochainComplex.SplitFactorization.comp_map_of_commSq Q f g ((b i).hom ≫ p i)
    ((b j).hom ≫ p j) u (d i).hom (d j).hom h₄ h₁

section Effective

variable [PerfectField k]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})]

set_option quotPrecheck false in
local notation "M" => effectiveReflection k

/-- The canonical map from the projective model to the relative effective
motive is an isomorphism for the original open pair. -/
@[no_expose]
def effectiveProjectivePairIso {U X : Sm} (j : U ⟶ X) [IsOpenImmersion j.left] :
    (singularPresheafToEffective k).obj ((projectivePairDerived k).obj (Arrow.mk j)) ≅
      effectivePairMotive k j :=
  ((sheafificationEffectiveReflectionIso k).app _).symm ≪≫
    (M).mapIso (asIso (projectivePairDerivedAugmentation k (Arrow.mk j)))

set_option maxHeartbeats 650000 in
-- The source is the same projective representative used in the augmentation.
omit [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}] in
/-- The projective comparison is the reflection comparison followed by the original augmentation. -/
theorem effectiveProjectivePairIso_hom {U X : Sm} (j : U ⟶ X)
    [IsOpenImmersion j.left] :
    let P := (projectivePairDerived k).obj (Arrow.mk j)
    (effectiveProjectivePairIso j).hom =
      (sheafificationEffectiveReflectionIso k).inv.app P ≫
        (M).map (projectivePairDerivedAugmentation k (Arrow.mk j)) := by
  unfold effectiveProjectivePairIso
  rfl

set_option maxHeartbeats 1000000 in
-- The comparison retains the original projective and effective pair maps.
omit [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}] in
/-- The projective model comparison is natural on open pairs. -/
theorem effectiveProjectivePairIso_naturality {U X U' X' : Sm}
    {i : U ⟶ X} {j : U' ⟶ X'} [IsOpenImmersion i.left] [IsOpenImmersion j.left]
    (φ : Arrow.mk i ⟶ Arrow.mk j) :
    (singularPresheafToEffective k).map ((projectivePairDerived k).map φ) ≫
        (effectiveProjectivePairIso j).hom =
      (effectiveProjectivePairIso i).hom ≫ (effectivePairMotiveFunctor k).map φ := by
  let f := (projectivePairDerived k).map φ
  let d := (sheafificationEffectiveReflectionIso k).inv
  let p (j : Arrow Sm) := projectivePairDerivedAugmentation k j
  let g := (singleTransferSheafMinus k).map ((transferPairCokernelFunctor k).map φ)
  let f₀ := (singularPresheafToEffective k).map f
  let f₁ := (derivedNisnevichSheafification k).map f
  let di := d.app ((projectivePairDerived k).obj (Arrow.mk i))
  let dj := d.app ((projectivePairDerived k).obj (Arrow.mk j))
  let pi := p (Arrow.mk i)
  let pj := p (Arrow.mk j)
  have h₁ : f₀ ≫ dj = di ≫ (M).map f₁ := d.naturality f
  have h₂ : f₁ ≫ pj = pi ≫ g := projectivePairDerivedAugmentation_naturality k φ
  have hc : f₀ ≫ (dj ≫ (M).map pj) = (di ≫ (M).map pi) ≫ (M).map g :=
    CochainComplex.SplitFactorization.comp_map_of_commSq (M) f₁ g pi pj f₀ di dj h₂ h₁
  exact (congrArg (f₀ ≫ ·) (effectiveProjectivePairIso_hom j)).trans
    (hc.trans (congrArg (· ≫ (M).map g) (effectiveProjectivePairIso_hom i).symm))

/-- The fixed effective parameter functor sends the original relative pair
to the relative motive of the literal product open. -/
@[no_expose]
def effectiveSmoothParameterPairIso {U X : Sm} (j : U ⟶ X) [IsOpenImmersion j.left] :
    (effectiveParameterTensor e).obj (effectivePairMotive k j) ≅
      effectivePairMotive k ((G).map j) := by
  let P := (projectivePairDerived k).obj (Arrow.mk j)
  exact (effectiveParameterTensor e).mapIso (effectiveProjectivePairIso j).symm ≪≫
    (effectiveParameterTensorCompIso e).app P ≪≫
    ((sheafificationEffectiveReflectionIso k).app ((derivedParameterPushforward F).obj P)).symm ≪≫
    (M).mapIso (asIso (projectiveSmoothParameterPairAugmentation e (Arrow.mk j)))

set_option maxHeartbeats 650000 in
-- Evaluate the four isomorphisms at their fixed projective and effective objects.
/-- The product comparison identifies the original projective model and quotient augmentation. -/
theorem effectiveSmoothParameterPairIso_hom {U X : Sm} (j : U ⟶ X)
    [IsOpenImmersion j.left] :
    let P := (projectivePairDerived k).obj (Arrow.mk j)
    let A := derivedParameterPushforward F
    (effectiveSmoothParameterPairIso e j).hom =
      (effectiveParameterTensor e).map (effectiveProjectivePairIso j).inv ≫
        (effectiveParameterTensorCompIso e).hom.app P ≫
        (sheafificationEffectiveReflectionIso k).inv.app (A.obj P) ≫
          (M).map (projectiveSmoothParameterPairAugmentation e (Arrow.mk j)) := by
  unfold effectiveSmoothParameterPairIso
  rfl

end Effective

section EffectiveParameterMap

variable {T' : SmoothSite (Spec (CommRingCat.of k))} {F' : Cor k ⥤ Cor k} [F'.Additive]
  (e' : Cor.graphFunctor k ⋙ F' ≅ parameterProduct T' ⋙ Cor.graphFunctor k)
  (g : T ⟶ T') (η : F ⟶ F')
  (hη : ∀ X : SmoothSite (Spec (CommRingCat.of k)), η.app (Cor.mk X) ≫ e'.hom.app X =
    e.hom.app X ≫ (Cor.graphFunctor k).map ((parameterMap g).app X))

set_option maxHeartbeats 1200000 in
-- The comparison retains the original projective and effective pair maps.
include hη in
/-- The projective pair augmentation sends a parameter map to the original product map. -/
theorem projectiveSmoothParameterPairAugmentation_parameter (j : Arrow Sm) :
    (derivedNisnevichSheafification k).map
        ((projectiveDerivedMinusFunctorMap (coendPushforwardParameterMap η)).app
          ((projectivePairDerived k).obj j)) ≫ projectiveSmoothParameterPairAugmentation e' j =
      projectiveSmoothParameterPairAugmentation e j ≫
        (singleTransferSheafMinus k).map
          ((transferPairCokernelFunctor k).map (smoothParameterArrowMap g j)) := by
  let a₀ := derivedNisnevichSheafification k
  let t := coendPushforwardParameterMap η
  let P := (projectivePairDerived k).obj j
  have ht : (projectiveDerivedMinusFunctorMap t).app P =
      (projectiveCoefficientNatTrans k t).app P := by
    let I := DerivedCategory.Minus.ι (C := PST)
    apply I.map_injective
    exact (projectiveDerivedMinusFunctorMap_map_app t P).trans
      (projectiveCoefficientNatTrans_app_hom k t P).symm
  rw [ht]
  apply ObjectProperty.hom_ext
  let d := projectivePairTermwiseModelIso k H j
  let d' := projectivePairTermwiseModelIso k (coendPushforward F') j
  let b := smoothParameterCochainAugmentation e j
  let b' := smoothParameterCochainAugmentation e' j
  let f := ((Functor.whiskerRight t a).mapHomologicalComplex c).app
    ((projectivePairCochain k).obj j)
  let r := (s).map ((transferPairCokernelFunctor k).map (smoothParameterArrowMap g j))
  let u := (a₀.map ((projectiveCoefficientNatTrans k t).app P)).hom
  have h₁ : u ≫ d'.hom = d.hom ≫ (Q).map f :=
    projectivePairTermwiseModelIso_coefficient k t j
  have h₂ : f ≫ b' = b ≫ r := smoothParameterCochainAugmentation_parameter e e' g η hη j
  exact CochainComplex.SplitFactorization.comp_map_of_commSq Q f r b b' u d.hom d'.hom h₂ h₁

variable [PerfectField k]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})]

set_option quotPrecheck false in
local notation "M" => effectiveReflection k

set_option maxHeartbeats 1200000 in
-- The comparison retains the original projective and effective pair maps.
include hη in
/-- Varying the smooth parameter gives the actual map of the corresponding product pairs. -/
theorem effectiveSmoothParameterPairIso_parameter {U X : Sm} (j : U ⟶ X) [IsOpenImmersion j.left] :
    (effectiveParameterTensorMap e e' η).app (effectivePairMotive k j) ≫
        (effectiveSmoothParameterPairIso e' j).hom =
      (effectiveSmoothParameterPairIso e j).hom ≫
        (effectivePairMotiveFunctor k).map (smoothParameterArrowMap g (Arrow.mk j)) := by
  let d := (sheafificationEffectiveReflectionIso k).inv
  let b := (effectiveParameterTensorCompIso e).hom
  let b' := (effectiveParameterTensorCompIso e').hom
  let T₀ := effectiveParameterTensor e
  let T₁ := effectiveParameterTensor e'
  let u := effectiveParameterTensorMap e e' η
  let P := (projectivePairDerived k).obj (Arrow.mk j)
  let f := (projectiveDerivedMinusFunctorMap (coendPushforwardParameterMap η)).app P
  let r := effectiveProjectivePairIso j
  let p := projectiveSmoothParameterPairAugmentation e (Arrow.mk j)
  let p' := projectiveSmoothParameterPairAugmentation e' (Arrow.mk j)
  let g' := (singleTransferSheafMinus k).map
    ((transferPairCokernelFunctor k).map (smoothParameterArrowMap g (Arrow.mk j)))
  rw [effectiveSmoothParameterPairIso_hom e' j, effectiveSmoothParameterPairIso_hom e j]
  change u.app _ ≫ T₁.map r.inv ≫ b'.app P ≫ d.app _ ≫ (M).map p' =
    (T₀.map r.inv ≫ b.app P ≫ d.app _ ≫ (M).map p) ≫ (M).map g'
  rw [← u.naturality_assoc r.inv, effectiveParameterTensorMap_app_localized,
    Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc, d.naturality_assoc f]
  simp only [Functor.comp_map, Category.assoc, ← (M).map_comp]
  exact congrArg (fun h => T₀.map r.inv ≫ b.app P ≫ d.app _ ≫ (M).map h)
    (projectiveSmoothParameterPairAugmentation_parameter e e' g η hη (Arrow.mk j))

end EffectiveParameterMap

end AlgebraicGeometry.MotivicHomotopy
