/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.SupportedProductCoverComparison
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.SmoothProductComparison
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.SignedExactness
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-! # Reflection of the derived product-pair tensor comparison -/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Category MonoidalCategory
open AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

private theorem represented_parameter_path {C : Type*} [Category* C]
    {X Y Y' Z T P Q W : C} (x : X ⟶ Y) (e : Y ⟶ Y')
    (b : Y ⟶ Z) (b' : Y' ⟶ T) (f : Z ⟶ T)
    (c : Y' ⟶ P) (d : P ⟶ Q) (a : T ≅ Q) (t : Q ⟶ W)
    (h₀ : b' = c ≫ d ≫ a.inv) (h₁ : e ≫ b' = b ≫ f) :
    x ≫ b ≫ f ≫ a.hom ≫ t = x ≫ e ≫ c ≫ d ≫ t := by
  rw [← reassoc_of% h₁, reassoc_of% h₀, a.inv_hom_id_assoc]

private theorem reflected_map_comp {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (A : C ⥤ D) (r : D ⥤ E) {q : C ⥤ E} (ε : q ⟶ A ⋙ r)
    {X Y Z : C} {W : D} (f : X ⟶ Y) (g : Y ⟶ Z) (p : A.obj Z ⟶ W) :
    ε.app X ≫ r.map (A.map (f ≫ g) ≫ p) = q.map f ≫ q.map g ≫ ε.app Z ≫ r.map p := by
  have h : q.map (f ≫ g) ≫ ε.app Z ≫ r.map p =
      ε.app X ≫ r.map (A.map (f ≫ g)) ≫ r.map p :=
    ε.naturality_assoc (f ≫ g) (r.map p)
  exact (congrArg (ε.app X ≫ ·) (r.map_comp _ _)).trans
    (h.symm.trans (q.map_comp_assoc _ _ _))

variable (k : Type u) [Field k] [PerfectField k]

/-- Nisnevich sheafification on the correspondence site at the coefficient universe. -/
local instance supportedProductCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

/-- Nisnevich sheafification on the smooth site at the coefficient universe. -/
local instance supportedProductSmoothSheafify :
    HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Sm(" K ")" => SmoothSite (Spec (CommRingCat.of K))
local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
set_option quotPrecheck false in
local notation "D" => DerivedCategory.Minus PST
local notation "E" => EffectiveMotivesMinus k
local notation "sₚ" => singleDerivedMinus k 0
local notation "A" => derivedNisnevichSheafification k
local notation "r" => effectiveReflection k
local notation "q" => singularPresheafToEffective k
local notation "M" => effectiveSmoothMotive k
set_option quotPrecheck false in
local notation "θ" => Cor.graphFunctorCompTensorRightIso (k := k)
local notation "γ" => Cor.graphFunctor k
local notation "C₀" => curriedTensor (Cor k)
set_option quotPrecheck false in
local notation "d" => derivedConvolutionTensorIso (k := k)
set_option quotPrecheck false in
local notation "Rₚ" => γ ⋙ representableLarge k
set_option quotPrecheck false in
local notation "R₀" => Rₚ ⋙ sₚ

/-- The canonical abelian structure on the transfer coefficients of the cover. -/
local instance supportedProductAbelian : Abelian NST := SheafWithTransfers.abelian k

attribute [local instance] derivedConvolutionMonoidalCategory derivedConvolutionCommShift₂Int

/-- The signed convolution on the effective motives of the cover. -/
local instance supportedProductMonoidal : MonoidalCategory E :=
  effectiveSignedConvolutionMonoidalCategory θ

/-- Signed convolution commutes with shifts in each argument. -/
local instance supportedProductCommShift₂Int : (curriedTensor E).CommShift₂Int :=
  effectiveSignedConvolutionCommShift₂Int θ

/-- The monoidal structure on the singular localization. -/
local instance supportedProductLocalizationMonoidal : (q).Monoidal :=
  (effectiveSignedConvolutionLocalizationCoreMonoidal θ).toMonoidal

/-- The singular localization tensorator respects the specified shifts. -/
local instance supportedProductLocalizationMonoidalCommShift : Functor.LaxMonoidal.CommShift q ℤ :=
  effectiveSignedConvolutionLocalizationMonoidalCommShift θ

variable {U V : Sm(k)} (j : U ⟶ V) [IsOpenImmersion j.left]

set_option quotPrecheck false in
local notation "P" => (projectivePairDerived k).obj (Arrow.mk j)
set_option quotPrecheck false in
local notation "F" => tensorLeft P ⋙ A

/-- The chosen tensor comparison before applying the pair transfer quotient. -/
def pairCoverToEffectiveCompIso :
    q ⋙ tensorLeft (effectivePairMotive k j) ≅ F ⋙ r := by
  let e := effectiveProjectivePairIso (k := k) j
  let b : tensorLeft ((q).obj P) ≅ tensorLeft (effectivePairMotive k j) :=
    (curriedTensor E).mapIso e
  exact Functor.isoWhiskerLeft q b.symm ≪≫ Functor.Monoidal.commTensorLeft q P ≪≫
    Functor.isoWhiskerLeft (tensorLeft P) (sheafificationEffectiveReflectionIso k).symm ≪≫
    (Functor.associator _ _ _).symm

private theorem pairCoverToEffectiveCompIso_hom_app (K : D) :
    (pairCoverToEffectiveCompIso k j).hom.app K =
      ((effectiveProjectivePairIso j).inv ▷ (q).obj K) ≫
        Functor.LaxMonoidal.μ q P K ≫
          (sheafificationEffectiveReflectionIso k).inv.app ((tensorLeft P).obj K) ≫ 𝟙 _ := by
  unfold pairCoverToEffectiveCompIso
  rfl

set_option maxHeartbeats 1100000 in
-- Compose the shift laws of the actual tensorator, reflection, and reassociation.
/-- The pair tensor comparison carries the specified integer shifts. -/
theorem pairCoverToEffectiveCompIso_commShift :
    NatTrans.CommShift (pairCoverToEffectiveCompIso k j).hom ℤ := by
  let e := effectiveProjectivePairIso (k := k) j
  let T := tensorLeft P
  let L := tensorLeft (effectivePairMotive k j)
  let L' := tensorLeft ((q).obj P)
  let b : L' ≅ L := (curriedTensor E).mapIso e
  let : NatTrans.CommShift b.hom ℤ :=
    inferInstanceAs (NatTrans.CommShift ((curriedTensor E).map e.hom) ℤ)
  let : NatTrans.CommShift b.inv ℤ := NatTrans.CommShift.of_iso_inv b ℤ
  let m := Functor.Monoidal.commTensorLeft q P
  have hm : NatTrans.CommShift m.hom ℤ := Functor.LaxMonoidal.CommShift.commShift_μNatTransSnd P
  let a := sheafificationEffectiveReflectionIso k
  let : NatTrans.CommShift a.hom ℤ := Functor.CommShift.ofIso_compatibility a ℤ
  let : NatTrans.CommShift a.inv ℤ := NatTrans.CommShift.of_iso_inv a ℤ
  let α := Functor.associator T A r
  let : NatTrans.CommShift α.hom ℤ :=
    inferInstanceAs (NatTrans.CommShift (Functor.associator T A r).hom ℤ)
  have hα : NatTrans.CommShift α.inv ℤ := NatTrans.CommShift.of_iso_inv α ℤ
  let x := Functor.whiskerLeft q b.inv
  let y := Functor.whiskerLeft T a.inv
  have hx : NatTrans.CommShift x ℤ := NatTrans.CommShift.whiskerLeft (F₁ := q) L L' b.inv ℤ
  have hy : NatTrans.CommShift y ℤ :=
    NatTrans.CommShift.whiskerLeft (F₁ := T) q (A ⋙ r) a.inv ℤ
  have h₁ : NatTrans.CommShift (y ≫ α.inv) ℤ :=
    @NatTrans.CommShift.comp _ _ _ _ _ _ _ y α.inv ℤ _ _ _ _ _ _ hy hα
  have h₂ : NatTrans.CommShift (m.hom ≫ y ≫ α.inv) ℤ :=
    @NatTrans.CommShift.comp _ _ _ _ _ _ _ m.hom (y ≫ α.inv) ℤ _ _ _ _ _ _ hm h₁
  change NatTrans.CommShift (x ≫ m.hom ≫ y ≫ α.inv) ℤ
  exact @NatTrans.CommShift.comp _ _ _ _ _ _ _ x (m.hom ≫ y ≫ α.inv) ℤ _ _ _ _ _ _ hx h₂

set_option maxHeartbeats 1500000 in
-- The localized tensorator is compared with the original product-pair endpoint.
/-- The reflected derived product map gives the original effective pair comparison. -/
theorem reflectedDerivedProductPairEndIso (Y : Sm(k)) :
    ((pairCoverToEffectiveCompIso k j).hom.app ((R₀).obj Y)) ≫
      (r).map (derivedProductPairEndIso k j Y).hom =
    (effectivePairMotive k j ◁ (localizedRepresentableIso (Cor.mk Y)).hom) ≫
      (effectivePairProductRightIso k j Y).hom := by
  let e := effectiveProjectivePairIso (k := k) j
  let b := effectiveRepresentedRightParameterIso θ Y
  let a := effectiveParameterTensorCompIso (θ Y)
  let c := (effectiveRepresentedRightCompIso θ Y).app P
  let d₁ := (derivedConvolutionParameterIso C₀ (Cor.mk Y)).app P
  let d₀ := ((d).app P).app ((R₀).obj Y)
  let L := localizedRepresentableIso (Cor.mk Y)
  let H := effectiveParameterTensor (θ Y)
  let p := projectiveSmoothParameterPairAugmentation (θ Y) (Arrow.mk j)
  let ε := (sheafificationEffectiveReflectionIso k).inv
  let m := Functor.LaxMonoidal.μ q P ((R₀).obj Y)
  have h₀ : b.hom.app ((q).obj P) = c.hom ≫ (q).map d₁.hom ≫ a.inv.app P :=
    effectiveRepresentedRightParameterIso_hom_app_localized θ Y P
  have h₁ :
      (e.inv ▷ (M).obj Y) ≫ b.hom.app ((q).obj P) =
        b.hom.app (effectivePairMotive k j) ≫ H.map e.inv :=
    b.hom.naturality e.inv
  have h₂ : (effectivePairMotive k j ◁ L.hom) ≫ (e.inv ▷ (M).obj Y) ≫ c.hom =
      (e.inv ▷ (q).obj ((R₀).obj Y)) ≫ m ≫ (q).map d₀.hom := by
    let X := (q).obj P
    let u := effectivePairMotive k j ◁ L.hom
    let v := e.inv ▷ (effectiveMotive k).obj (Cor.mk Y)
    let h := X ◁ L.hom
    let i := X ◁ L.inv
    let a₀ := e.inv ▷ (q).obj ((R₀).obj Y)
    let z := m ≫ (q).map d₀.hom
    have hex : u ≫ v = a₀ ≫ h := whisker_exchange e.inv L.hom
    have hi : h ≫ i = 𝟙 _ :=
      (whiskerLeft_comp X L.hom L.inv).symm.trans
        ((congrArg (X ◁ ·) L.hom_inv_id).trans (whiskerLeft_id _ _))
    change u ≫ v ≫ i ≫ z = a₀ ≫ z
    calc
      _ = (u ≫ v) ≫ i ≫ z := (Category.assoc _ _ _).symm
      _ = (a₀ ≫ h) ≫ i ≫ z := congrArg (· ≫ i ≫ z) hex
      _ = a₀ ≫ (h ≫ i) ≫ z :=
        (Category.assoc _ _ _).trans (congrArg (a₀ ≫ ·) (Category.assoc _ _ _).symm)
      _ = a₀ ≫ 𝟙 _ ≫ z := congrArg (fun t => a₀ ≫ t ≫ z) hi
      _ = _ := congrArg (a₀ ≫ ·) (Category.id_comp z)
  rw [pairCoverToEffectiveCompIso_hom_app]
  change _ = (effectivePairMotive k j ◁ L.hom) ≫
    (b.hom.app (effectivePairMotive k j) ≫ (effectiveSmoothParameterPairIso (θ Y) j).hom)
  rw [effectiveSmoothParameterPairIso_hom]
  simp only [Category.comp_id]
  change ((e.inv ▷ (q).obj ((R₀).obj Y)) ≫
    m ≫ ε.app ((tensorLeft P).obj ((R₀).obj Y))) ≫
      (r).map ((A).map (d₀.hom ≫ d₁.hom) ≫ p) =
    (effectivePairMotive k j ◁ L.hom) ≫
      (b.hom.app (effectivePairMotive k j) ≫ H.map e.inv ≫ a.hom.app P ≫
        ε.app _ ≫ (r).map p)
  let x := effectivePairMotive k j ◁ L.hom
  let v := e.inv ▷ (effectiveMotive k).obj (Cor.mk Y)
  let z := e.inv ▷ (q).obj ((R₀).obj Y)
  let t := ε.app ((derivedParameterPushforward ((C₀).flip.obj (Cor.mk Y))).obj P) ≫
    (r).map p
  let g := (r).map ((A).map (d₀.hom ≫ d₁.hom) ≫ p)
  let h := (q).map d₁.hom ≫ t
  have hL := reflected_map_comp A r ε d₀.hom d₁.hom p
  have hR := represented_parameter_path x v (b.hom.app (effectivePairMotive k j))
    (b.hom.app ((q).obj P)) (H.map e.inv) c.hom ((q).map d₁.hom) (a.app P) t h₀ h₁
  calc
    _ = (z ≫ m) ≫ ε.app _ ≫ g :=
      (congrArg (· ≫ g) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _)
    _ = (z ≫ m) ≫ (q).map d₀.hom ≫ h := congrArg ((z ≫ m) ≫ ·) hL
    _ = (z ≫ m ≫ (q).map d₀.hom) ≫ h :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ h) (Category.assoc _ _ _))
    _ = (x ≫ v ≫ c.hom) ≫ h := congrArg (· ≫ h) h₂.symm
    _ = x ≫ v ≫ c.hom ≫ h :=
      (Category.assoc _ _ _).trans (congrArg (x ≫ ·) (Category.assoc _ _ _))
    _ = _ := hR.symm

end AlgebraicGeometry.MotivicHomotopy
