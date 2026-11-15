/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.CoherentConvolution
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedSingleMonoidal
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedSingleShiftNaturality
import Mathlib.CategoryTheory.Localization.Monoidal.Braided

/-! # The braiding of represented motives with their cochain sign -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory AlgebraicGeometry.Scheme Opposite

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable {k : Type u} [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)] [MonoidalPreadditive (Cor k)]

local notation "E" => EffectiveMotivesMinus k
set_option quotPrecheck false in
local notation "q" => singularPresheafToEffective k
local notation "F" => curriedTensor (Cor k)
local notation "s" => BraidedCategory.curriedBraidingNatIso (Cor k)
local notation "y" => representableLarge k
set_option quotPrecheck false in
local notation "J(" X "," n ")" => (singleDerivedMinus k n).obj ((y).obj X)

/-- The abelian structure of the transfer sheaves used in the represented braiding comparison. -/
local instance representedBraidingSheafAbelian : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

attribute [local instance] derivedConvolutionMonoidalCategory derivedConvolutionSymmetricCategory

set_option maxHeartbeats 650000 in
-- Evaluate the actual correspondence on the universal coend generators.
omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
private theorem convolutionRepresentableIso_braiding (X Y : Cor k) :
    convolutionSwapHom F s ((y).obj X) ((y).obj Y) ≫ (convolutionRepresentableIso F Y X).hom =
      (convolutionRepresentableIso F X Y).hom ≫ (y).map (β_ X Y).hom := by
  apply convolutionPresheaf_hom_ext
  intro U V W p q₀ a
  change ULift.{u + 1} (V ⟶ X) at p
  change ULift.{u + 1} (W ⟶ Y) at q₀
  obtain ⟨p⟩ := p
  obtain ⟨q₀⟩ := q₀
  let t := convolutionGenerator F ((y).obj X) ((y).obj Y) U V W (ULift.up p) (ULift.up q₀) a
  change (convolutionRepresentableIso F Y X).hom.hom.app (op U)
      ((convolutionSwapHom F s ((y).obj X) ((y).obj Y)).hom.app (op U) t) =
    ((y).map (β_ X Y).hom).hom.app (op U)
      ((convolutionRepresentableIso F X Y).hom.hom.app (op U) t)
  dsimp only [t]
  rw [convolutionSwapHom_generator, convolutionRepresentableIso_hom_generator,
    convolutionRepresentableIso_hom_generator, representableLarge_map_app_apply]
  apply congrArg ULift.up
  have hβ : ((s).hom.app V).app W = (β_ V W).hom := (rfl)
  have hTensor {A A' B B' : Cor k} (f : A ⟶ A') (g : B ⟶ B') :
      convolutionCorrespondenceMap F f g = f ⊗ₘ g := (MonoidalCategory.tensorHom_def f g).symm
  rw [hβ, hTensor, hTensor]
  exact (Category.assoc _ _ _).trans
    ((congrArg (a ≫ ·) (BraidedCategory.braiding_naturality p q₀).symm).trans
      (Category.assoc _ _ _).symm)

/-- The tensor of localized represented complexes in one cochain degree
is the localized product representable in the sum degree. -/
def localizedRepresentedTensorIso
    (e : ∀ T : SmoothSite (Spec (.of k)),
      Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
        SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k) (X Y : Cor k) (n : ℤ) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    (q).obj (J(X,n)) ⊗ (q).obj (J(Y,n)) ≅ (q).obj (J(X ⊗ Y,n + n)) :=
  letI := effectiveSignedConvolutionMonoidalCategory e
  let K := J(X,n)
  let L := J(Y,n)
  let V := singleDerivedMinus k (n + n)
  let d := derivedConvolutionSingleTensorIso ((y).obj X) ((y).obj Y) n
  let h := (effectiveSignedConvolutionLocalizationCoreMonoidal e).μIso K L
  let c : V.obj (((convolutionBifunctor F).obj ((y).obj X)).obj ((y).obj Y)) ≅
      J(X ⊗ Y,n + n) := V.mapIso (convolutionRepresentableIso F X Y)
  h ≪≫ (q).mapIso (d ≪≫ c)

set_option maxHeartbeats 650000 in
-- Use the braiding component of the original two-variable localization.
private theorem effectiveSignedConvolutionLocalization_braiding
    (e : ∀ T : SmoothSite (Spec (.of k)),
      Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
        SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)
    (K L : DerivedCategory.Minus (TransferCoefficients k)) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    letI := effectiveSignedConvolutionSymmetricCategory e
    (β_ ((q).obj K) ((q).obj L)).hom ≫
        ((effectiveSignedConvolutionLocalizationCoreMonoidal e).μIso L K).hom =
      ((effectiveSignedConvolutionLocalizationCoreMonoidal e).μIso K L).hom ≫
        (q).map (β_ K L).hom := by
  let := effectiveSignedConvolutionMonoidalCategory e
  let := effectiveSignedConvolutionSymmetricCategory e
  let w := effectivePresheafEquivalences k
  let d := derivedConvolutionTensorIso (k := k)
  let hs := curriedCorrespondenceBraiding_involutive (k := k)
  let : w.IsMonoidal := effectivePresheafEquivalences_isMonoidal F e s hs d
  let ε := effectiveLocalizationUnitIso (k := k)
  let m := (effectiveSignedConvolutionLocalizationCoreMonoidal e).μIso K L
  let m' := (effectiveSignedConvolutionLocalizationCoreMonoidal e).μIso L K
  have h := Localization.Monoidal.β_hom_app q w ε K L
  have hβ : (β_ ((q).obj K) ((q).obj L)).hom = m.hom ≫ (q).map (β_ K L).hom ≫ m'.inv := h
  have hCancel : ((q).map (β_ K L).hom ≫ m'.inv) ≫ m'.hom = (q).map (β_ K L).hom := by
    rw [Category.assoc, m'.inv_hom_id, Category.comp_id]
  exact (congrArg (· ≫ m'.hom) hβ).trans
    ((Category.assoc _ _ _).trans (congrArg (m.hom ≫ ·) hCancel))

set_option maxHeartbeats 650000 in
-- Compose the original localization, single and representable naturality squares.
/-- The comparison in a single cochain degree preserves the tensor of the
original signed finite-correspondence maps in both variables. -/
@[reassoc]
theorem localizedRepresentedTensorIso_naturality
    (e : ∀ T : SmoothSite (Spec (.of k)),
      Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
        SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k) {X X' Y Y' : Cor k}
    (f : X ⟶ X') (g : Y ⟶ Y') (n : ℤ) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    let s₀ := singleDerivedMinus k n
    let s₁ := singleDerivedMinus k (n + n)
    ((q).map (s₀.map ((y).map f)) ⊗ₘ (q).map (s₀.map ((y).map g))) ≫
        (localizedRepresentedTensorIso e X' Y' n).hom =
      (localizedRepresentedTensorIso e X Y n).hom ≫
        (q).map (s₁.map ((y).map (f ⊗ₘ g))) := by
  let := effectiveSignedConvolutionMonoidalCategory e
  let s₀ := singleDerivedMinus k n
  let s₁ := singleDerivedMinus k (n + n)
  change ((q).map (s₀.map ((y).map f)) ⊗ₘ (q).map (s₀.map ((y).map g))) ≫ _ = _
  let h := (effectiveSignedConvolutionLocalizationCoreMonoidal e)
  let a := s₀.map ((y).map f)
  let b := s₀.map ((y).map g)
  let A := derivedConvolutionSingleTensorIso ((y).obj X) ((y).obj Y) n
  let A' := derivedConvolutionSingleTensorIso ((y).obj X') ((y).obj Y') n
  let B := convolutionRepresentableIso F X Y
  let B' := convolutionRepresentableIso F X' Y'
  have hμ :
      ((q).map a ⊗ₘ (q).map b) ≫ (h.μIso (J(X',n)) (J(Y',n))).hom =
        (h.μIso (J(X,n)) (J(Y,n))).hom ≫ (q).map (a ⊗ₘ b) := by
    rw [MonoidalCategory.tensorHom_def, Category.assoc, h.μIso_hom_natural_right,
      h.μIso_hom_natural_left_assoc, ← (q).map_comp, ← MonoidalCategory.tensorHom_def]
  have hA : (a ⊗ₘ b) ≫ A'.hom =
      A.hom ≫ s₁.map (convolutionMap F ((y).map f) ((y).map g)) :=
    derivedConvolutionSingle_naturality ((y).map f) ((y).map g) n
  have hB : s₁.map (convolutionMap F ((y).map f) ((y).map g)) ≫ s₁.map B'.hom =
      s₁.map B.hom ≫ s₁.map ((y).map (f ⊗ₘ g)) := by
    have hf : convolutionCorrespondenceMap F f g = f ⊗ₘ g :=
      (MonoidalCategory.tensorHom_def f g).symm
    rw [← s₁.map_comp, ← s₁.map_comp, ← hf]
    exact s₁.congr_map (convolutionRepresentableIso_naturality F f g)
  change ((q).map a ⊗ₘ (q).map b) ≫ (h.μIso (J(X',n)) (J(Y',n))).hom ≫
      (q).map (A'.hom ≫ s₁.map B'.hom) =
    ((h.μIso (J(X,n)) (J(Y,n))).hom ≫ (q).map (A.hom ≫ s₁.map B.hom)) ≫
      (q).map (s₁.map ((y).map (f ⊗ₘ g)))
  rw [reassoc_of% hμ, ← (q).map_comp, ← Category.assoc (a ⊗ₘ b), hA, Category.assoc, hB,
    ← Category.assoc A.hom, (q).map_comp, Category.assoc]

set_option maxHeartbeats 650000 in
-- Apply the localization tensorator and the cochain sign in their original order.
/-- Braiding on the original localized represented complexes is the original
correspondence swap with the Koszul coefficient `(-1)^(n*n)`. -/
theorem localizedRepresentedTensorIso_braiding
    (e : ∀ T : SmoothSite (Spec (.of k)),
      Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
        SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k) (X Y : Cor k) (n : ℤ) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    letI := effectiveSignedConvolutionSymmetricCategory e
    (β_ ((q).obj (J(X,n))) ((q).obj (J(Y,n)))).hom ≫
        (localizedRepresentedTensorIso e Y X n).hom =
      (n * n).negOnePow • ((localizedRepresentedTensorIso e X Y n).hom ≫
        (q).map ((singleDerivedMinus k (n + n)).map ((y).map (β_ X Y).hom))) := by
  let := effectiveSignedConvolutionMonoidalCategory e
  let := effectiveSignedConvolutionSymmetricCategory e
  let S := singleDerivedMinus k (n + n)
  let x := J(X,n)
  let y₀ := J(Y,n)
  let d := derivedConvolutionSingleTensorIso ((y).obj X) ((y).obj Y) n
  let d' := derivedConvolutionSingleTensorIso ((y).obj Y) ((y).obj X) n
  let c := convolutionRepresentableIso F X Y
  let c' := convolutionRepresentableIso F Y X
  let s₀ := convolutionSwapHom F s ((y).obj X) ((y).obj Y)
  let m := (effectiveSignedConvolutionLocalizationCoreMonoidal e).μIso x y₀
  let m' := (effectiveSignedConvolutionLocalizationCoreMonoidal e).μIso y₀ x
  let h := (y).map (β_ X Y).hom
  let r := (n * n).negOnePow
  have hC : S.map s₀ ≫ S.map c'.hom = S.map c.hom ≫ S.map h := by
    rw [← S.map_comp, ← S.map_comp]
    exact S.congr_map (convolutionRepresentableIso_braiding X Y)
  have hD : (β_ x y₀).hom ≫ d'.hom = r • (d.hom ≫ S.map s₀) :=
    derivedConvolutionSingle_braiding ((y).obj X) ((y).obj Y) n
  have hD' : (β_ x y₀).hom ≫ (d'.hom ≫ S.map c'.hom) =
      r • ((d.hom ≫ S.map c.hom) ≫ S.map h) := by
    calc
      _ = ((β_ x y₀).hom ≫ d'.hom) ≫ S.map c'.hom := (Category.assoc _ _ _).symm
      _ = _ := by
        rw [hD, Linear.units_smul_comp, Category.assoc d.hom, hC, ← Category.assoc d.hom]
  have hE : (β_ ((q).obj x) ((q).obj y₀)).hom ≫ m'.hom =
      m.hom ≫ (q).map (β_ x y₀).hom :=
    effectiveSignedConvolutionLocalization_braiding e x y₀
  change (β_ ((q).obj x) ((q).obj y₀)).hom ≫
      (m'.hom ≫ (q).map (d'.hom ≫ S.map c'.hom)) =
    r • ((m.hom ≫ (q).map (d.hom ≫ S.map c.hom)) ≫ (q).map (S.map h))
  calc
    _ = ((β_ ((q).obj x) ((q).obj y₀)).hom ≫ m'.hom) ≫
        (q).map (d'.hom ≫ S.map c'.hom) := (Category.assoc _ _ _).symm
    _ = (m.hom ≫ (q).map (β_ x y₀).hom) ≫ (q).map (d'.hom ≫ S.map c'.hom) :=
      congrArg (· ≫ (q).map (d'.hom ≫ S.map c'.hom)) hE
    _ = m.hom ≫ (q).map ((β_ x y₀).hom ≫ (d'.hom ≫ S.map c'.hom)) := by
      exact (Category.assoc _ _ _).trans (congrArg (m.hom ≫ ·) ((q).map_comp _ _).symm)
    _ = m.hom ≫ (q).map (r • ((d.hom ≫ S.map c.hom) ≫ S.map h)) :=
      congrArg (fun t => m.hom ≫ (q).map t) hD'
    _ = _ := by rw [Functor.map_units_smul, (q).map_comp, Linear.comp_units_smul, Category.assoc]

/-- The localization of a representable placed in degree `n` is its original
effective motive shifted by `[-n]`. -/
def localizedRepresentableShiftIso (X : Cor k) (n : ℤ) :
    (((effectiveMotive k).obj X)⟦-n⟧) ≅ (q).obj (J(X,n)) :=
  (shiftFunctor E (-n)).mapIso (localizedRepresentableIso X).symm ≪≫
    ((q).commShiftIso (-n)).symm.app (J(X,0)) ≪≫
    (q).mapIso (singleDerivedMinusShiftIso ((y).obj X) n)

omit [HasDerivedCategory AddCommGrpCat.{u + 1}] [MonoidalCategory (Cor k)]
  [SymmetricCategory (Cor k)] [MonoidalPreadditive (Cor k)] in
/-- The shifted comparison retains the original finite-correspondence map. -/
@[reassoc]
theorem localizedRepresentableShiftIso_naturality {X Y : Cor k} (f : X ⟶ Y) (n : ℤ) :
    (shiftFunctor E (-n)).map ((effectiveMotive k).map f) ≫
        (localizedRepresentableShiftIso Y n).hom =
      (localizedRepresentableShiftIso X n).hom ≫
        (q).map ((singleDerivedMinus k n).map ((y).map f)) := by
  let I := localizedRepresentableIso (k := k)
  let sh := shiftFunctor E (-n)
  let d := (q).commShiftIso (-n)
  let t := (singleDerivedMinus k 0).map ((y).map f)
  have h : (effectiveMotive k).map f ≫ (I Y).inv = (I X).inv ≫ (q).map t := by
    apply (cancel_epi (I X).hom).1
    rw [← Category.assoc, ← localizedRepresentableIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  change sh.map ((effectiveMotive k).map f) ≫ sh.map (I Y).inv ≫
      d.inv.app (J(Y,0)) ≫ (q).map (singleDerivedMinusShiftIso ((y).obj Y) n).hom =
    (sh.map (I X).inv ≫ d.inv.app (J(X,0)) ≫
      (q).map (singleDerivedMinusShiftIso ((y).obj X) n).hom) ≫
      (q).map ((singleDerivedMinus k n).map ((y).map f))
  let shD := shiftFunctor (DerivedCategory.Minus (TransferCoefficients k)) (-n)
  let u := (singleDerivedMinusShiftIso ((y).obj X) n).hom
  let v := (singleDerivedMinusShiftIso ((y).obj Y) n).hom
  let m := (singleDerivedMinus k n).map ((y).map f)
  have hd : sh.map ((q).map t) ≫ d.inv.app (J(Y,0)) =
      d.inv.app (J(X,0)) ≫ (q).map (shD.map t) := d.inv.naturality t
  have hm : shD.map t ≫ v = u ≫ m := singleDerivedMinusShiftIso_naturality ((y).map f) n
  have hq : (q).map (shD.map t) ≫ (q).map v = (q).map u ≫ (q).map m :=
    (((q).map_comp _ _).symm.trans ((q).congr_map hm)).trans ((q).map_comp _ _)
  rw [← sh.map_comp_assoc, h, sh.map_comp, Category.assoc, reassoc_of% hd, hq]
  simp only [Category.assoc]
  rfl

/-- The shift-zero product comparison for the original effective motives. -/
def effectiveRepresentedTensorIso
    (e : ∀ T : SmoothSite (Spec (.of k)),
      Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
        SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k) (X Y : Cor k) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    (effectiveMotive k).obj X ⊗ (effectiveMotive k).obj Y ≅ (effectiveMotive k).obj (X ⊗ Y) :=
  letI := effectiveSignedConvolutionMonoidalCategory e
  let l := localizedRepresentableIso (k := k)
  let z : (q).obj (J(X ⊗ Y,0 + 0)) ≅ (effectiveMotive k).obj (X ⊗ Y) := l (X ⊗ Y)
  ((l X).symm ⊗ᵢ (l Y).symm) ≪≫ localizedRepresentedTensorIso e X Y 0 ≪≫ z

/-- The original represented effective product comparison is natural
with respect to both signed finite correspondences. -/
@[reassoc]
theorem effectiveRepresentedTensorIso_naturality
    (e : ∀ T : SmoothSite (Spec (.of k)),
      Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
        SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k) {X X' Y Y' : Cor k}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    letI := effectiveSignedConvolutionMonoidalCategory e
    let m := effectiveMotive k
    (m.map f ⊗ₘ m.map g) ≫ (effectiveRepresentedTensorIso e X' Y').hom =
      (effectiveRepresentedTensorIso e X Y).hom ≫ m.map (f ⊗ₘ g) := by
  let := effectiveSignedConvolutionMonoidalCategory e
  let m := effectiveMotive k
  change (m.map f ⊗ₘ m.map g) ≫ _ = _
  let l := localizedRepresentableIso (k := k)
  let s₀ := singleDerivedMinus k 0
  have hl {A B : Cor k} (v : A ⟶ B) :
      m.map v ≫ (l B).inv = (l A).inv ≫ (q).map (s₀.map ((y).map v)) := by
    apply (cancel_epi (l A).hom).1
    rw [← Category.assoc, ← localizedRepresentableIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  simp only [effectiveRepresentedTensorIso, Iso.trans_hom, tensorIso_hom, Iso.symm_hom,
    Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, hl f, hl g, ← tensorHom_comp_tensorHom_assoc,
    localizedRepresentedTensorIso_naturality_assoc]
  let L := (l X).inv ⊗ₘ (l Y).inv
  let C := (localizedRepresentedTensorIso e X Y 0).hom
  let h := f ⊗ₘ g
  let t := (q).map ((singleDerivedMinus k (0 + 0)).map ((y).map h))
  have hn : t ≫ (l (X' ⊗ Y')).hom = (l (X ⊗ Y)).hom ≫ m.map h :=
    localizedRepresentableIso_naturality h
  exact congrArg (fun v => L ≫ C ≫ v) hn

/-- On smooth motives the actual effective braiding corresponds to the
original symmetry of finite correspondences. -/
theorem effectiveRepresentedTensorIso_braiding
    (e : ∀ T : SmoothSite (Spec (.of k)),
      Cor.graphFunctor k ⋙ (F).flip.obj (Cor.mk T) ≅
        SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k) (X Y : Cor k) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    letI := effectiveSignedConvolutionSymmetricCategory e
    (β_ ((effectiveMotive k).obj X) ((effectiveMotive k).obj Y)).hom ≫
        (effectiveRepresentedTensorIso e Y X).hom =
      (effectiveRepresentedTensorIso e X Y).hom ≫ (effectiveMotive k).map (β_ X Y).hom := by
  let := effectiveSignedConvolutionMonoidalCategory e
  let := effectiveSignedConvolutionSymmetricCategory e
  simp only [effectiveRepresentedTensorIso, Iso.trans_hom, Category.assoc, tensorIso_hom,
    Iso.symm_hom]
  rw [← BraidedCategory.braiding_naturality_assoc]
  let L := (localizedRepresentableIso X).inv ⊗ₘ (localizedRepresentableIso Y).inv
  let c := (localizedRepresentedTensorIso e X Y 0).hom
  let c' := (localizedRepresentedTensorIso e Y X 0).hom
  let h := (β_ X Y).hom
  let t := (q).map ((singleDerivedMinus k (0 + 0)).map ((y).map h))
  have hB : (β_ ((q).obj (J(X,0))) ((q).obj (J(Y,0)))).hom ≫ c' = c ≫ t := by
    have hh : (β_ ((q).obj (J(X,0))) ((q).obj (J(Y,0)))).hom ≫ c' =
        ((0 : ℤ) * 0).negOnePow • (c ≫ t) := localizedRepresentedTensorIso_braiding e X Y 0
    simpa only [mul_zero, Int.negOnePow_zero, one_smul] using hh
  have hN : t ≫ (localizedRepresentableIso (Y ⊗ X)).hom =
      (localizedRepresentableIso (X ⊗ Y)).hom ≫ (effectiveMotive k).map h :=
    localizedRepresentableIso_naturality h
  change L ≫ (β_ ((q).obj (J(X,0))) ((q).obj (J(Y,0)))).hom ≫ c' ≫
      (localizedRepresentableIso (Y ⊗ X)).hom =
    L ≫ c ≫ (localizedRepresentableIso (X ⊗ Y)).hom ≫ (effectiveMotive k).map h
  rw [reassoc_of% hB, hN]

end AlgebraicGeometry.MotivicHomotopy
