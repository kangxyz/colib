/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.IntegralParameterNaturality
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.ReducedTorusComparison
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.SignedExactness
import Colib.CategoryTheory.Localization.LiftNatIso
import Colib.CategoryTheory.Preadditive.ComplementComparison
import Colib.CategoryTheory.Retract.Intertwining

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
  change H.map (𝟙 R - t) ≫ v = v ≫ (r).map (𝟙 U - p)
  exact Functor.map_complement_comp_of_intertwining H r hx hy ht hq

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
  let src : Retract (q ⋙ tensorRight R₀) (q ⋙ tensorRight R) :=
    s.map ((curriedTensor E).flip ⋙ (Functor.whiskeringLeft D E E).obj q)
  let projectiveRetract : Retract (projectiveReducedTorusTensorToDerivedMinus k)
      (projectiveTorusTensorToDerivedMinus k) :=
    ⟨incl, quot, NatTrans.ext (funext (projectiveReducedTorusTensorSection_quotient (k := k)))⟩
  let tgt : Retract N₀ (projectiveTorusTensorToDerivedMinus k ⋙ r) :=
    projectiveRetract.map ((Functor.whiskeringRight D _ E).obj r)
  have h (K : D) : (src.r.app K ≫ src.i.app K) ≫ C.hom.app K =
      C.hom.app K ≫ tgt.r.app K ≫ tgt.i.app K := by
    change (((q).obj K ◁ s.r) ≫ ((q).obj K ◁ s.i)) ≫ C.hom.app K =
      C.hom.app K ≫ (r).map ((quot).app K) ≫ (r).map ((incl).app K)
    rw [← whiskerLeft_comp, hs, ← (r).map_comp,
      projectiveReducedTorusTensorQuotient_section]
    exact effectiveNativeParameterCompIso_projector e d b hu hp K
  exact src.isoOfIntertwining tgt C (NatTrans.ext (funext h))

/-- The original reduced comparison is the section, Laurent comparison, and quotient. -/
theorem reducedTorusCompIso_hom :
    letI := effectiveSignedConvolutionMonoidalCategory e
    (reducedTorusCompIso e d b hu hp s hs).hom =
      Functor.whiskerLeft q ((curriedTensor E).flip.map s.i) ≫
        (effectiveNativeParameterCompIso e G d).hom ≫ Functor.whiskerRight quot r := by
  unfold reducedTorusCompIso
  exact Retract.isoOfIntertwining_hom _ _ _ _

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
  let c₀ := reducedTorusCompIso e d b hu hp s hs
  let g := sheafificationEffectiveReflectionIso k
  let c₁ : N₀ ≅ q ⋙ T := projectiveEffectiveTorusNatIso k ≪≫ Functor.isoWhiskerRight g T
  have h : (effectiveRightReducedTorusIso e d b hu hp s hs).hom.app ((q).obj K) =
      c₀.hom.app K ≫ c₁.hom.app K :=
    Localization.liftNatIso_refl_hom_app q W N₀ c₀ c₁ K
  rw [h]
  simp only [c₀, c₁, g, reducedTorusCompIso_hom, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app, Category.assoc]
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
