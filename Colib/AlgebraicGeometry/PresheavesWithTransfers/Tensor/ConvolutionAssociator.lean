/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionDay
public import Colib.CategoryTheory.Preadditive.IntegralConvolutionDayComparison
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionFunctor
public import Mathlib.CategoryTheory.Monoidal.DayConvolution
public import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Preadditive

public import Colib.AlgebraicGeometry.Correspondences.Coproducts.Binary

/-!
# Associator of the signed convolution

Mathlib's Day associator applies to the pointwise extension on the
original integral coefficient modules. Full faithfulness transports
it back to the existing convolution of transfer presheaves.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory
open scoped MonoidalCategory.ExternalProduct DayConvolution TensorProduct

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K
local notation "MZ(" K ")" => IntegerCoefficients K

/-- Regard the original additive transfer coefficients as ordinary integer-module presheaves. -/
def convolutionForget : PST(k) ⥤ ((Cor k)ᵒᵖ ⥤ MZ(k)) :=
  forget ⋙ (Functor.whiskeringRight _ _ _).obj integerModuleFunctor

/-- The coefficient realization is fully faithful. -/
def convolutionForgetFullyFaithful : (convolutionForget (k := k)).FullyFaithful := by
  let V := forget₂ (MZ(k)) AddCommGrpCat.{u + 1}
  let e : integerModuleFunctor ⋙ V ≅ 𝟭 AddCommGrpCat.{u + 1} :=
    NatIso.ofComponents (fun _ => Iso.refl _)
  let h := (Functor.FullyFaithful.id AddCommGrpCat.{u + 1}).ofIso e.symm
  let hM := Functor.FullyFaithful.ofCompFaithful h
  exact (ObjectProperty.fullyFaithfulι (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{u + 1})).comp
    (hM.whiskeringRight (Cor k)ᵒᵖ)

variable [MonoidalCategory (Cor k)] [MonoidalPreadditive (Cor k)]

local notation "F(" K ")" => curriedTensor (Cor K)

/-- The product on opposite correspondences is the opposite of the selected signed product. -/
def convolutionOppositeTensorIso :
    (prodOpEquiv (D := Cor k) (Cor k)).inverse ⋙
        (Functor.uncurry.obj (F(k))).op ≅ tensor (Cor k)ᵒᵖ :=
  CategoryTheory.Preadditive.Convolution.oppositeTensorIso.{u + 1, u} (C := Cor k)

/-- The pointwise extension unit along the product on opposite correspondences. -/
def convolutionDayUnit (P Q : PST(k)) :
    convolutionExternalProduct P Q ⟶
      tensor (Cor k)ᵒᵖ ⋙ (convolutionForget (k := k)).obj (convolutionPresheaf (F(k)) P Q) :=
  CategoryTheory.Preadditive.Convolution.dayUnit.{u + 1, u, 0} P.obj Q.obj

/-- The original integral coend has the pointwise extension property for the opposite product. -/
theorem convolutionDayUnit_isPointwiseLeftKanExtension (P Q : PST(k)) (X : (Cor k)ᵒᵖ) :
    Nonempty ((Functor.LeftExtension.mk _
      (convolutionDayUnit P Q)).IsPointwiseLeftKanExtensionAt X) :=
  CategoryTheory.Preadditive.Convolution.dayUnit_isPointwiseLeftKanExtension.{u + 1, u, 0}
    P.obj Q.obj X

/-- The original convolution is a pointwise Day extension of the coefficient tensor. -/
@[colib_tag "COL-1302", instance_reducible]
def convolutionDayComparison (P Q : PST(k)) :
    DayConvolution ((convolutionForget (k := k)).obj P) (convolutionForget.obj Q) where
  convolution := (convolutionForget (k := k)).obj (convolutionPresheaf (F(k)) P Q)
  unit := convolutionDayUnit P Q
  isPointwiseLeftKanExtensionUnit X :=
    Classical.choice (convolutionDayUnit_isPointwiseLeftKanExtension P Q X)

/-- The Day extension unit acts on the same literal identity generator as the coend unit. -/
theorem convolutionDayUnit_tmul (P Q : PST(k)) (X Y : Cor k)
    (x : sections P X) (y : sections Q Y) :
    let W := convolutionForget (k := k)
    letI := convolutionDayComparison P Q
    (DayConvolution.unit (W.obj P) (W.obj Q)).app (op X, op Y) (x ⊗ₜ[ℤ] y) =
      convolutionGenerator (F(k)) P Q (X ⊗ Y) X Y x y (𝟙 _) := by
  intro W
  let := convolutionDayComparison P Q
  let G := W.obj (convolutionPresheaf (F(k)) P Q)
  change G.map (𝟙 (op (X ⊗ Y))) (convolutionKanExtensionUnitApp (F(k)) P Q X Y
      (x ⊗ₜ[ℤ] y)) = _
  rw [G.map_id, ModuleCat.id_apply]
  exact convolutionKanExtensionUnitApp_tmul (F(k)) P Q X Y x y

/-- The Day map is the realization of the actual convolution coefficient map. -/
theorem convolutionForget_map_eq_dayMap {P P' Q Q' : PST(k)} (f : P ⟶ P') (g : Q ⟶ Q') :
    let W := convolutionForget (k := k)
    letI := convolutionDayComparison P Q
    letI := convolutionDayComparison P' Q'
    W.map (convolutionMap (F(k)) f g) = DayConvolution.map (W.map f) (W.map g) := by
  intro W
  let := convolutionDayComparison P Q
  let := convolutionDayComparison P' Q'
  apply Functor.hom_ext_of_isLeftKanExtension _ (DayConvolution.unit (W.obj P) (W.obj Q))
  apply NatTrans.ext
  funext YZ
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro p q
  obtain ⟨Y, Z⟩ := YZ
  change sections P Y.unop at p
  change sections Q Z.unop at q
  let X := Y.unop ⊗ Z.unop
  let U := DayConvolution.unit (W.obj P) (W.obj Q)
  let V := DayConvolution.unit (W.obj P') (W.obj Q')
  let m := W.map (convolutionMap (F(k)) f g)
  let n := DayConvolution.map (W.map f) (W.map g)
  let p' := f.hom.app Y p
  let q' := g.hom.app Z q
  have h₁ := convolutionDayUnit_tmul P Q Y.unop Z.unop p q
  have h₂ := convolutionDayUnit_tmul P' Q' Y.unop Z.unop p' q'
  have hm := convolutionMap_generator (F(k)) f g X Y.unop Z.unop p q (𝟙 _)
  have h := ConcreteCategory.congr_hom
    (DayConvolution.unit_app_map_app (W.map f) (W.map g) Y Z) (p ⊗ₜ[ℤ] q)
  change n.app (op X) (U.app (Y, Z) (p ⊗ₜ[ℤ] q)) =
    V.app (Y, Z) (p' ⊗ₜ[ℤ] q') at h
  change m.app (op X) (U.app (Y, Z) (p ⊗ₜ[ℤ] q)) =
    n.app (op X) (U.app (Y, Z) (p ⊗ₜ[ℤ] q))
  exact ((congrArg (m.app (op X)) h₁).trans (hm.trans h₂.symm)).trans h.symm

/-- The associator on the original integral coend of transfer presheaves. -/
def convolutionAssociator (P Q R : PST(k)) :
    convolutionPresheaf (F(k)) (convolutionPresheaf (F(k)) P Q) R ≅
      convolutionPresheaf (F(k)) P (convolutionPresheaf (F(k)) Q R) := by
  let W := convolutionForget (k := k)
  let : ∀ P Q : PST(k), DayConvolution (W.obj P) (W.obj Q) := convolutionDayComparison
  let : DayConvolution (W.obj P) (W.obj Q ⊛ W.obj R) :=
    convolutionDayComparison P (convolutionPresheaf (F(k)) Q R)
  let : DayConvolution (W.obj P ⊛ W.obj Q) (W.obj R) :=
    convolutionDayComparison (convolutionPresheaf (F(k)) P Q) R
  exact convolutionForgetFullyFaithful.preimageIso
    (DayConvolution.associator (W.obj P) (W.obj Q) (W.obj R))

/-- The component of the Day associator on a triple with identity inner label. -/
private theorem convolutionAssociator_identity_generator (P Q R : PST(k))
    (X Y Z : Cor k) (x : sections P X) (y : sections Q Y) (z : sections R Z) :
    (convolutionAssociator P Q R).hom.hom.app (op ((X ⊗ Y) ⊗ Z))
      (convolutionGenerator (F(k)) (convolutionPresheaf (F(k)) P Q) R
        ((X ⊗ Y) ⊗ Z) (X ⊗ Y) Z
        (convolutionGenerator (F(k)) P Q (X ⊗ Y) X Y x y (𝟙 _)) z (𝟙 _)) =
      convolutionGenerator (F(k)) P (convolutionPresheaf (F(k)) Q R)
        ((X ⊗ Y) ⊗ Z) X (Y ⊗ Z) x
        (convolutionGenerator (F(k)) Q R (Y ⊗ Z) Y Z y z (𝟙 _)) (α_ X Y Z).hom := by
  let W := convolutionForget (k := k)
  let : ∀ P Q : PST(k), DayConvolution (W.obj P) (W.obj Q) := convolutionDayComparison
  let : DayConvolution (W.obj P) (W.obj Q ⊛ W.obj R) :=
    convolutionDayComparison P (convolutionPresheaf (F(k)) Q R)
  let : DayConvolution (W.obj P ⊛ W.obj Q) (W.obj R) :=
    convolutionDayComparison (convolutionPresheaf (F(k)) P Q) R
  have h := ConcreteCategory.congr_hom
    (DayConvolution.associator_hom_unit_unit (W.obj P) (W.obj Q) (W.obj R)
      (op X) (op Y) (op Z)) ((x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] z)
  have hα := convolutionForgetFullyFaithful.map_preimage
    (DayConvolution.associator (W.obj P) (W.obj Q) (W.obj R)).hom
  change W.map (convolutionAssociator P Q R).hom = _ at hα
  rw [← hα] at h
  let PQ := convolutionPresheaf (F(k)) P Q
  let QR := convolutionPresheaf (F(k)) Q R
  let A := DayConvolution.unit (W.obj P) (W.obj Q)
  let B := DayConvolution.unit (W.obj Q) (W.obj R)
  let L := DayConvolution.unit (W.obj PQ) (W.obj R)
  let J := DayConvolution.unit (W.obj P) (W.obj QR)
  let X₀ := op ((X ⊗ Y) ⊗ Z)
  let m := (W.map (convolutionAssociator P Q R).hom).app X₀
  let g := (W.obj (convolutionPresheaf (F(k)) P QR)).map (α_ X Y Z).hom.op
  change m (L.app (op (X ⊗ Y), op Z) ((A.app (op X, op Y) (x ⊗ₜ[ℤ] y)) ⊗ₜ[ℤ] z)) =
    g (J.app (op X, op (Y ⊗ Z)) (x ⊗ₜ[ℤ] (B.app (op Y, op Z) (y ⊗ₜ[ℤ] z)))) at h
  rw [show A.app (op X, op Y) (x ⊗ₜ[ℤ] y) =
      convolutionGenerator (F(k)) P Q (X ⊗ Y) X Y x y (𝟙 _) from
      convolutionDayUnit_tmul P Q X Y x y,
    show B.app (op Y, op Z) (y ⊗ₜ[ℤ] z) =
      convolutionGenerator (F(k)) Q R (Y ⊗ Z) Y Z y z (𝟙 _) from
      convolutionDayUnit_tmul Q R Y Z y z] at h
  let s := convolutionGenerator (F(k)) P Q (X ⊗ Y) X Y x y (𝟙 _)
  let t := convolutionGenerator (F(k)) Q R (Y ⊗ Z) Y Z y z (𝟙 _)
  have hL : L.app (op (X ⊗ Y), op Z) (s ⊗ₜ[ℤ] z) =
      convolutionGenerator (F(k)) PQ R ((X ⊗ Y) ⊗ Z) (X ⊗ Y) Z s z (𝟙 _) :=
    convolutionDayUnit_tmul PQ R (X ⊗ Y) Z s z
  have hR : J.app (op X, op (Y ⊗ Z)) (x ⊗ₜ[ℤ] t) =
      convolutionGenerator (F(k)) P QR (X ⊗ (Y ⊗ Z)) X (Y ⊗ Z) x t (𝟙 _) :=
    convolutionDayUnit_tmul P QR X (Y ⊗ Z) x t
  have hG := convolutionPresheaf_transfer_generator (F(k)) P QR (α_ X Y Z).hom
    X (Y ⊗ Z) x t (𝟙 _)
  rw [Category.comp_id] at hG
  exact (congrArg m hL).symm.trans (h.trans ((congrArg g hR).trans hG))

/-- The original associator acts on the two correspondence labels by composition and
reassociation. -/
theorem convolutionAssociator_hom_generator (P Q R : PST(k))
    (U V X Y Z : Cor k) (x : sections P X) (y : sections Q Y) (z : sections R Z)
    (a : V ⟶ X ⊗ Y) (b : U ⟶ V ⊗ Z) :
    (convolutionAssociator P Q R).hom.hom.app (op U)
      (convolutionGenerator (F(k)) (convolutionPresheaf (F(k)) P Q) R U V Z
        (convolutionGenerator (F(k)) P Q V X Y x y a) z b) =
      convolutionGenerator (F(k)) P (convolutionPresheaf (F(k)) Q R) U X (Y ⊗ Z) x
        (convolutionGenerator (F(k)) Q R (Y ⊗ Z) Y Z y z (𝟙 _))
        (b ≫ (a ▷ Z) ≫ (α_ X Y Z).hom) := by
  let P' := convolutionPresheaf (F(k)) P Q
  let C := convolutionPresheaf (F(k)) P' R
  let D := convolutionPresheaf (F(k)) P (convolutionPresheaf (F(k)) Q R)
  let t := convolutionGenerator (F(k)) P Q (X ⊗ Y) X Y x y (𝟙 _)
  let d := b ≫ a ▷ Z
  have ht : transfer P' a t = convolutionGenerator (F(k)) P Q V X Y x y a := by
    rw [convolutionPresheaf_transfer_generator, Category.comp_id]
  have hz : transfer R (𝟙 Z) z = z := by simp
  have hlabel : convolutionCorrespondenceMap (F(k)) a (𝟙 Z) = a ▷ Z := by
    change (a ▷ Z) ≫ (X ⊗ Y) ◁ 𝟙 Z = a ▷ Z
    rw [whiskerLeft_id, Category.comp_id]
  have hmove := convolutionGenerator_transfer (F(k)) P' R a (𝟙 Z) t z b
  rw [ht, hz, hlabel] at hmove
  let t' := convolutionGenerator (F(k)) P' R ((X ⊗ Y) ⊗ Z) (X ⊗ Y) Z t z (𝟙 _)
  have hn := ConcreteCategory.congr_hom
    (transfer_naturality (convolutionAssociator P Q R).hom d) t'
  change (convolutionAssociator P Q R).hom.hom.app (op U) (transfer C d t') =
    transfer D d ((convolutionAssociator P Q R).hom.hom.app (op ((X ⊗ Y) ⊗ Z)) t') at hn
  rw [show t' = convolutionGenerator (F(k)) P' R ((X ⊗ Y) ⊗ Z) (X ⊗ Y) Z t z (𝟙 _) from rfl,
    convolutionPresheaf_transfer_generator, Category.comp_id,
    convolutionAssociator_identity_generator, convolutionPresheaf_transfer_generator] at hn
  rw [hmove]
  simpa only [d, Category.assoc] using hn

/-- The actual convolution associator is natural in all three coefficients. -/
theorem convolutionAssociator_naturality {P P' Q Q' R R' : PST(k)}
    (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R') :
    convolutionMap (F(k)) (convolutionMap (F(k)) f g) h ≫
        (convolutionAssociator P' Q' R').hom =
      (convolutionAssociator P Q R).hom ≫ convolutionMap (F(k)) f (convolutionMap (F(k)) g h) := by
  let W := convolutionForget (k := k)
  let : ∀ P Q : PST(k), DayConvolution (W.obj P) (W.obj Q) := convolutionDayComparison
  let : DayConvolution (W.obj P) (W.obj Q ⊛ W.obj R) :=
    convolutionDayComparison P (convolutionPresheaf (F(k)) Q R)
  let : DayConvolution (W.obj P ⊛ W.obj Q) (W.obj R) :=
    convolutionDayComparison (convolutionPresheaf (F(k)) P Q) R
  let : DayConvolution (W.obj P') (W.obj Q' ⊛ W.obj R') :=
    convolutionDayComparison P' (convolutionPresheaf (F(k)) Q' R')
  let : DayConvolution (W.obj P' ⊛ W.obj Q') (W.obj R') :=
    convolutionDayComparison (convolutionPresheaf (F(k)) P' Q') R'
  apply convolutionForgetFullyFaithful.map_injective
  simp only [Functor.map_comp, convolutionForget_map_eq_dayMap]
  simp only [convolutionAssociator, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage]
  exact DayConvolution.associator_naturality (W.map f) (W.map g) (W.map h)

/-- The Day pentagon for the actual convolution and its coefficient maps. -/
theorem convolutionAssociator_pentagon (P Q R S : PST(k)) :
    convolutionMap (F(k)) (convolutionAssociator P Q R).hom (𝟙 S) ≫
        (convolutionAssociator P (convolutionPresheaf (F(k)) Q R) S).hom ≫
          convolutionMap (F(k)) (𝟙 P) (convolutionAssociator Q R S).hom =
      (convolutionAssociator (convolutionPresheaf (F(k)) P Q) R S).hom ≫
        (convolutionAssociator P Q (convolutionPresheaf (F(k)) R S)).hom := by
  let W := convolutionForget (k := k)
  let wP := W.obj P
  let wQ := W.obj Q
  let wR := W.obj R
  let wS := W.obj S
  let : ∀ P Q : PST(k), DayConvolution (W.obj P) (W.obj Q) := convolutionDayComparison
  let : DayConvolution (wP ⊛ wQ) wR :=
    convolutionDayComparison (convolutionPresheaf (F(k)) P Q) R
  let : DayConvolution wP (wQ ⊛ wR) :=
    convolutionDayComparison P (convolutionPresheaf (F(k)) Q R)
  let : DayConvolution (wQ ⊛ wR) wS :=
    convolutionDayComparison (convolutionPresheaf (F(k)) Q R) S
  let : DayConvolution wQ (wR ⊛ wS) :=
    convolutionDayComparison Q (convolutionPresheaf (F(k)) R S)
  let : DayConvolution ((wP ⊛ wQ) ⊛ wR) wS :=
    convolutionDayComparison (convolutionPresheaf (F(k))
      (convolutionPresheaf (F(k)) P Q) R) S
  let : DayConvolution (wP ⊛ wQ) (wR ⊛ wS) :=
    convolutionDayComparison (convolutionPresheaf (F(k)) P Q) (convolutionPresheaf (F(k)) R S)
  let : DayConvolution (wP ⊛ wQ ⊛ wR) wS :=
    convolutionDayComparison (convolutionPresheaf (F(k)) P
      (convolutionPresheaf (F(k)) Q R)) S
  let : DayConvolution wP (wQ ⊛ wR ⊛ wS) :=
    convolutionDayComparison P (convolutionPresheaf (F(k)) Q (convolutionPresheaf (F(k)) R S))
  let : DayConvolution wP ((wQ ⊛ wR) ⊛ wS) :=
    convolutionDayComparison P (convolutionPresheaf (F(k)) (convolutionPresheaf (F(k)) Q R) S)
  let hW := convolutionForgetFullyFaithful (k := k)
  apply hW.map_injective
  simp only [Functor.map_comp, convolutionForget_map_eq_dayMap]
  simp only [convolutionAssociator, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage]
  exact DayConvolution.pentagon wP wQ wR wS

end AlgebraicGeometry.PresheafWithTransfers
