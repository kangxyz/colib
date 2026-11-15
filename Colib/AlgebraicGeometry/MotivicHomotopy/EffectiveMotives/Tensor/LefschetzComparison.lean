/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.IntegralParameterNaturality
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.ReducedTorusComparison
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.SignedExactness

/-!
# Right tensor by the shifted reduced torus

The two splittings of the complement of the torus unit-section projector
are compared on the original projective models. Effective localization
descends this comparison, and the cochain shift in the second variable
produces the comparison for the Lefschetz object.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory AlgebraicGeometry.Scheme

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers
open SmoothSite SmoothSite.Contraction

variable {k : Type u} [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)] [MonoidalPreadditive (Cor k)]

local notation "PST" => TransferCoefficients k
set_option quotPrecheck false in
local notation "D" => DerivedCategory.Minus PST
local notation "E" => EffectiveMotivesMinus k
local notation "q" => singularPresheafToEffective k
local notation "W" => effectivePresheafEquivalences k
local notation "a" => derivedNisnevichSheafification k
local notation "M" => effectiveMotive k
local notation "r" => effectiveReflection k
local notation "γ" => Cor.graphFunctor k
local notation "S" => Spec (CommRingCat.of k)
local notation "G" => SmoothSite.multiplicativeGroupObject S
set_option quotPrecheck false in
local notation "B₀" => SmoothSite.base S
local notation "u₀" => SmoothSite.torusOne S
set_option quotPrecheck false in
local notation "p₀" => toBase G
local notation "T" => effectiveReducedTorusTensorFunctor k

/-- The abelian structure underlying the effective reduced torus comparison. -/
local instance lefschetzComparisonAbelian : Abelian (LargeSheaves k) := SheafWithTransfers.abelian k

variable (e : ∀ X : SmoothSite (Spec (CommRingCat.of k)),
  Cor.graphFunctor k ⋙ (curriedTensor (Cor k)).flip.obj (Cor.mk X) ≅
    SmoothSite.Contraction.parameterProduct X ⋙ Cor.graphFunctor k)

variable
  (d : (curriedTensor (Cor k)).flip.obj
      (Cor.mk (multiplicativeGroupObject (Spec (CommRingCat.of k)))) ≅
    Cor.parameterProduct (multiplicativeGroupObject (Spec (CommRingCat.of k))))
  (b : (curriedTensor (Cor k)).flip.obj (Cor.mk (base (Spec (CommRingCat.of k)))) ≅
    Cor.parameterProduct (base (Spec (CommRingCat.of k))))

variable
  (hu : (curriedTensor (Cor k)).flip.map
      ((Cor.graphFunctor k).map (SmoothSite.torusOne (Spec (CommRingCat.of k)))) ≫ d.hom =
    b.hom ≫ Cor.parameterProductMap (SmoothSite.torusOne (Spec (CommRingCat.of k))))
  (hp : (curriedTensor (Cor k)).flip.map
      ((Cor.graphFunctor k).map (toBase (multiplicativeGroupObject (Spec (CommRingCat.of k))))) ≫
        b.hom =
    d.hom ≫ Cor.parameterProductMap (toBase (multiplicativeGroupObject (Spec (CommRingCat.of k)))))

private def projectiveTorusProjectorHom :
    projectiveTorusTensorToDerivedMinus k ⟶ projectiveTorusTensorToDerivedMinus k :=
  Functor.whiskerRight (projectiveCoefficientNatTrans k
    (torusParameterTensorProjection k ≫ torusParameterTensorUnit k)) a

omit [PerfectField k] [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]
  [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)] [MonoidalPreadditive (Cor k)] in
private theorem projectiveTorusProjectorHom_app (K : D) :
    (projectiveTorusProjectorHom (k := k)).app K =
      (a).map ((projectiveCoefficientNatTrans k (torusParameterTensorProjection k)).app K) ≫
      (a).map ((projectiveCoefficientNatTrans k (torusParameterTensorUnit k)).app K) := by
  let p := torusParameterTensorProjection k
  let u := torusParameterTensorUnit k
  change (a).map ((projectiveCoefficientNatTrans k (p ≫ u)).app K) = _
  rw [← (a).map_comp]
  apply (a).congr_map
  apply ObjectProperty.hom_ext
  let C := ((boundedAboveProjectiveEquivalence k).inverse.obj K).obj
  let c := ComplexShape.up ℤ
  let P := (p.mapHomotopyCategory c).app C
  let U := (u.mapHomotopyCategory c).app C
  let Q : HomotopyCategory PST c ⥤ DerivedCategory PST := DerivedCategory.Qh
  have hp₀ := projectiveCoefficientNatTrans_app_hom k p K
  have hu₀ := projectiveCoefficientNatTrans_app_hom k u K
  have hpu := projectiveCoefficientNatTrans_app_hom k (p ≫ u) K
  change ((projectiveCoefficientNatTrans k (p ≫ u)).app K).hom =
    ((projectiveCoefficientNatTrans k p).app K).hom ≫
      ((projectiveCoefficientNatTrans k u).app K).hom
  rw [hpu, hp₀, hu₀, NatTrans.mapHomotopyCategory_comp, NatTrans.comp_app]
  exact Q.map_comp P U

set_option quotPrecheck false in
local notation "N₀" => projectiveReducedTorusTensorToDerivedMinus k ⋙ r
set_option quotPrecheck false in
local notation "R" => (M).obj ((Cor.graphFunctor k).obj G)
local notation "incl" => projectiveReducedTorusTensorSection k
local notation "quot" => projectiveReducedTorusTensorQuotient k

include hu hp in
private theorem effectiveNativeParameterCompIso_projector (K : D) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    let t : R ⟶ R := (M).map ((γ).map (p₀ ≫ u₀))
    ((q).obj K ◁ (𝟙 R - t)) ≫
        (effectiveNativeParameterCompIso e G d).hom.app K =
      (effectiveNativeParameterCompIso e G d).hom.app K ≫
        (r).map (𝟙 _ - (projectiveTorusProjectorHom (k := k)).app K) := by
  let := effectiveSignedConvolutionMonoidalCategory e
  let C := effectiveNativeParameterCompIso e G d
  let Z := (q).obj K
  let := effectiveSignedConvolutionMonoidalPreadditive e
  let H := tensorLeft Z
  let U := (projectiveTorusTensorToDerivedMinus k).obj K
  let v : H.obj R ⟶ (r).obj U := C.hom.app K
  let t : R ⟶ R := (M).map ((γ).map (p₀ ≫ u₀))
  let p := (projectiveTorusProjectorHom (k := k)).app K
  let h₁ := effectiveNativeParameterCompIso_naturality e d b p₀ hp K
  let h₂ := effectiveNativeParameterCompIso_naturality e b d u₀ hu K
  rw [← torusParameterTensorProjection_eq_mate k] at h₁
  rw [← torusParameterTensorUnit_eq_mate k] at h₂
  change (Z ◁ (M).map ((γ).map p₀)) ≫ (effectiveNativeParameterCompIso e B₀ b).hom.app K =
    C.hom.app K ≫ (a ⋙ r).map ((projectiveCoefficientNatTrans k
      (torusParameterTensorProjection k)).app K) at h₁
  change (Z ◁ (M).map ((γ).map u₀)) ≫ C.hom.app K =
    (effectiveNativeParameterCompIso e B₀ b).hom.app K ≫
      (a ⋙ r).map ((projectiveCoefficientNatTrans k (torusParameterTensorUnit k)).app K) at h₂
  have hp₀ : H.map t ≫ v = v ≫ (r).map p := by
    let x := (M).map ((γ).map p₀)
    let y := (M).map ((γ).map u₀)
    let v₀ := (effectiveNativeParameterCompIso e B₀ b).hom.app K
    let pn := (a).map ((projectiveCoefficientNatTrans k (torusParameterTensorProjection k)).app K)
    let un := (a).map ((projectiveCoefficientNatTrans k (torusParameterTensorUnit k)).app K)
    have ht : t = x ≫ y :=
      ((M).congr_map ((γ).map_comp p₀ u₀)).trans ((M).map_comp _ _)
    have hq : p = pn ≫ un := projectiveTorusProjectorHom_app K
    have hx : H.map x ≫ v₀ = v ≫ (r).map pn := h₁
    have hy : H.map y ≫ v = v₀ ≫ (r).map un := h₂
    calc
      _ = (H.map x ≫ H.map y) ≫ v :=
        congrArg (· ≫ v) ((H.congr_map ht).trans (H.map_comp x y))
      _ = H.map x ≫ (H.map y ≫ v) := Category.assoc _ _ _
      _ = H.map x ≫ (v₀ ≫ (r).map un) := congrArg (H.map x ≫ ·) hy
      _ = (H.map x ≫ v₀) ≫ (r).map un := (Category.assoc _ _ _).symm
      _ = (v ≫ (r).map pn) ≫ (r).map un := congrArg (· ≫ (r).map un) hx
      _ = v ≫ (r).map p :=
        (Category.assoc _ _ _).trans
          (congrArg (v ≫ ·) (((r).map_comp pn un).symm.trans ((r).congr_map hq.symm)))
  change H.map (𝟙 R - t) ≫ v = v ≫ (r).map (𝟙 U - p)
  exact (congrArg (· ≫ v) (H.map_sub (f := 𝟙 R) (g := t))).trans
    ((Preadditive.sub_comp _ _ _).trans
      ((congrArg₂ Sub.sub ((congrArg (· ≫ v) (H.map_id R)).trans (Category.id_comp v)) hp₀).trans
        ((congrArg (· - (v ≫ (r).map p))
          (((congrArg (v ≫ ·) ((r).map_id U)).trans (Category.comp_id v)).symm)).trans
          ((Preadditive.comp_sub _ _ _).symm.trans
            (congrArg (v ≫ ·) ((r).map_sub (f := 𝟙 U) (g := p)).symm)))))

private def isoOfIntertwiningRetracts {C : Type*} [Category* C] {A A' X Y : C}
    (j : A ⟶ X) (l : X ⟶ A) (i : A' ⟶ Y) (p : Y ⟶ A') (e : X ≅ Y)
    (hl : j ≫ l = 𝟙 A) (hp : i ≫ p = 𝟙 A')
    (h : (l ≫ j) ≫ e.hom = e.hom ≫ p ≫ i) : A ≅ A' where
  hom := j ≫ e.hom ≫ p
  inv := i ≫ e.inv ≫ l
  hom_inv_id := by
    simp only [Category.assoc]
    have h' : e.hom ≫ p ≫ i ≫ e.inv ≫ l = l ≫ j ≫ l := by
      rw [← Category.assoc p i, ← Category.assoc e.hom, ← h, Category.assoc,
        Iso.hom_inv_id_assoc, Category.assoc]
    rw [h', ← Category.assoc j l, hl, Category.id_comp]
  inv_hom_id := by
    simp only [Category.assoc]
    have h' : l ≫ j ≫ e.hom ≫ p = e.hom ≫ p ≫ i ≫ p := by
      simpa only [Category.assoc] using congrArg (· ≫ p) h
    rw [h', e.inv_hom_id_assoc, ← Category.assoc i p, hp, Category.id_comp]

omit [HasDerivedCategory AddCommGrpCat.{u + 1}] in
private theorem isoOfIntertwiningRetracts_hom {C : Type*} [Category* C] {A A' X Y : C}
    (j : A ⟶ X) (l : X ⟶ A) (i : A' ⟶ Y) (p : Y ⟶ A') (e : X ≅ Y)
    (hl : j ≫ l = 𝟙 A) (hp : i ≫ p = 𝟙 A')
    (h : (l ≫ j) ≫ e.hom = e.hom ≫ p ≫ i) :
    (isoOfIntertwiningRetracts j l i p e hl hp h).hom = j ≫ e.hom ≫ p := by
  unfold isoOfIntertwiningRetracts
  rfl

variable {R₀ : EffectiveMotivesMinus k}
  (s : Retract R₀ ((effectiveMotive k).obj
    (Cor.mk (multiplicativeGroupObject (Spec (CommRingCat.of k))))))
  (hs : s.r ≫ s.i = 𝟙 _ - (effectiveMotive k).map ((Cor.graphFunctor k).map
    (toBase (multiplicativeGroupObject (Spec (CommRingCat.of k))) ≫
      SmoothSite.torusOne (Spec (CommRingCat.of k)))))

include hu hp hs in
/-- The original projector comparison before effective localization. -/
@[no_expose]
def reducedTorusCompIso :
    letI := effectiveSignedConvolutionMonoidalCategory e
    q ⋙ tensorRight R₀ ≅ N₀ := by
  letI := effectiveSignedConvolutionMonoidalCategory e
  let C := effectiveNativeParameterCompIso e G d
  let j : q ⋙ tensorRight R₀ ⟶ q ⋙ tensorRight R :=
    Functor.whiskerLeft q ((curriedTensor E).flip.map s.i)
  let l : q ⋙ tensorRight R ⟶ q ⋙ tensorRight R₀ :=
    Functor.whiskerLeft q ((curriedTensor E).flip.map s.r)
  let P := Functor.whiskerRight quot r
  let I := Functor.whiskerRight incl r
  have h₁ (K : D) : j.app K ≫ l.app K = 𝟙 _ := by
    change ((q).obj K ◁ s.i) ≫ ((q).obj K ◁ s.r) = 𝟙 _
    rw [← whiskerLeft_comp, s.retract, whiskerLeft_id]
  have h₂ (K : D) : I.app K ≫ P.app K = 𝟙 _ := by
    change (r).map ((incl).app K) ≫ (r).map ((quot).app K) = 𝟙 _
    rw [← (r).map_comp, projectiveReducedTorusTensorSection_quotient, (r).map_id]
  have h₃ (K : D) : (l.app K ≫ j.app K) ≫ C.hom.app K =
      C.hom.app K ≫ P.app K ≫ I.app K := by
    change (((q).obj K ◁ s.r) ≫ ((q).obj K ◁ s.i)) ≫ C.hom.app K =
      C.hom.app K ≫ (r).map ((quot).app K) ≫ (r).map ((incl).app K)
    rw [← whiskerLeft_comp, hs, ← (r).map_comp,
      projectiveReducedTorusTensorQuotient_section]
    exact effectiveNativeParameterCompIso_projector e d b hu hp K
  exact isoOfIntertwiningRetracts j l I P C
    (NatTrans.ext (funext h₁)) (NatTrans.ext (funext h₂)) (NatTrans.ext (funext h₃))

/-- The original reduced comparison is the section, Laurent comparison, and quotient. -/
theorem reducedTorusCompIso_hom :
    letI := effectiveSignedConvolutionMonoidalCategory e
    (reducedTorusCompIso e d b hu hp s hs).hom =
      Functor.whiskerLeft q ((curriedTensor E).flip.map s.i) ≫
        (effectiveNativeParameterCompIso e G d).hom ≫ Functor.whiskerRight quot r := by
  unfold reducedTorusCompIso
  exact isoOfIntertwiningRetracts_hom _ _ _ _ _ _ _ _

include hu hp hs in
/-- Right tensor by the original split reduced torus is its native
effective reduced torus tensor. Its comparison is formed by the
literal inclusion followed by the original projective quotient. -/
def effectiveRightReducedTorusIso :
    letI := effectiveSignedConvolutionMonoidalCategory e
    tensorRight R₀ ≅ T := by
  letI := effectiveSignedConvolutionMonoidalCategory e
  let L := tensorRight R₀
  let g := sheafificationEffectiveReflectionIso k
  let C := projectiveEffectiveTorusNatIso k ≪≫ Functor.isoWhiskerRight g T
  let : Localization.Lifting q W N₀ L := ⟨reducedTorusCompIso e d b hu hp s hs⟩
  let : Localization.Lifting q W N₀ T := ⟨C.symm⟩
  exact Localization.liftNatIso q W N₀ N₀ L T (Iso.refl _)

/-- On a localized projective model, the reduced comparison uses the same
coefficient quotient and section as the original torus adjunction. -/
theorem effectiveRightReducedTorusIso_hom_app_localized (K : D) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    (effectiveRightReducedTorusIso e d b hu hp s hs).hom.app ((q).obj K) =
      ((q).obj K ◁ s.i) ≫ (effectiveNativeParameterCompIso e G d).hom.app K ≫
        (r).map ((quot).app K) ≫ (projectiveEffectiveTorusNatIso k).hom.app K ≫
          (T).map ((sheafificationEffectiveReflectionIso k).hom.app K) := by
  let := effectiveSignedConvolutionMonoidalCategory e
  rw [effectiveRightReducedTorusIso, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  simp only [reducedTorusCompIso_hom, Iso.refl_hom, Iso.symm_inv,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, NatTrans.comp_app,
    NatTrans.id_app, Category.id_comp, Category.assoc]
  rfl

/-- The second signed shift comparison, natural in the first effective motive. -/
def effectiveTensorRightShiftIso (K : E) (n : ℤ) :
    letI := effectiveSignedConvolutionMonoidalCategory e
    tensorRight (K⟦n⟧) ≅ tensorRight K ⋙ shiftFunctor E n := by
  letI := effectiveSignedConvolutionMonoidalCategory e
  letI := effectiveSignedConvolutionCommShift₂Int e
  let B := curriedTensor E
  exact NatIso.ofComponents (fun P => ((B.obj P).commShiftIso n).app K) (by
    intro P Q f
    exact (NatTrans.shift_app_comm (B.map f) n K).symm)

include hu hp hs in
/-- Right tensor by the shift of the reduced torus agrees with the
original reduced torus tensor followed by the cochain shift by one. -/
def effectiveRightLefschetzIso :
    letI := effectiveSignedConvolutionMonoidalCategory e
    tensorRight (R₀⟦(1 : ℤ)⟧) ≅ T ⋙ shiftFunctor E (1 : ℤ) :=
  effectiveTensorRightShiftIso e R₀ 1 ≪≫
    Functor.isoWhiskerRight (effectiveRightReducedTorusIso e d b hu hp s hs)
      (shiftFunctor E (1 : ℤ))

end AlgebraicGeometry.MotivicHomotopy
