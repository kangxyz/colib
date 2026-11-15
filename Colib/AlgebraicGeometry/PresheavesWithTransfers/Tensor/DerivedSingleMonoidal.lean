/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedMonoidalTransport
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.CochainSingleMonoidal
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.HomotopyMonoidalQuotient
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctorSingleNaturality
import Mathlib.Algebra.Homology.Linear

/-! # The signed derived tensor of projective single complexes -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)]
  [MonoidalPreadditive (Cor k)] [HasDerivedCategory.{w} (TransferCoefficients k)]

local notation "PST" => TransferCoefficients k
local notation "F" => curriedTensor (Cor k)
local notation "B" => convolutionBifunctor F
set_option quotPrecheck false in
local notation "D" => DerivedCategory.Minus PST
local notation "E" => boundedAboveProjectiveEquivalence k

attribute [local instance] convolutionHomotopyMonoidalCategory convolutionHomotopySymmetricCategory
  boundedAboveProjectiveCondition_convolution_isMonoidal

attribute [local instance] derivedConvolutionMonoidalCategory derivedConvolutionSymmetricCategory

/-- The transported tensor symmetry is the image of the symmetry on the chosen projective models. -/
theorem derivedConvolution_braiding_map (K L : D) :
    (β_ K L).hom =
      (E).functor.map (β_ ((E).inverse.obj K) ((E).inverse.obj L)).hom := by
  rfl

/-- Compare the tensor of actual projective singles with the degree-sum single
of the original coefficient convolution. -/
def derivedConvolutionSingleTensorIso (P Q : PST) [Projective P] [Projective Q] (n : ℤ) :
    (singleDerivedMinus k n).obj P ⊗ (singleDerivedMinus k n).obj Q ≅
      (singleDerivedMinus k (n + n)).obj (((B).obj P).obj Q) := by
  let C := (CochainComplex.singleFunctor PST n).obj P
  let C' := (CochainComplex.singleFunctor PST n).obj Q
  let c := ComplexShape.up ℤ
  let H := HomotopyCategory.quotient PST c
  let d := HomologicalComplex.mapBifunctorSingleSingleIso B P Q n n
  let V := DerivedCategory.Minus.ι (C := PST)
  let p := singleProjectiveComparison P n
  let q := singleProjectiveComparison Q n
  refine (E).functor.mapIso (p ⊗ᵢ q) ≪≫ V.preimageIso ?_
  change DerivedCategory.Qh.obj (H.obj (HomologicalComplex.mapBifunctor C C' B c)) ≅
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor PST (n + n)).obj (((B).obj P).obj Q))
  exact DerivedCategory.Qh.mapIso (H.mapIso d) ≪≫ (DerivedCategory.quotientCompQhIso PST).app _

private theorem derivedConvolutionSingleTensorIso_map_hom
    (P Q : PST) [Projective P] [Projective Q] (n : ℤ) :
    let V := DerivedCategory.Minus.ι (C := PST)
    let U := (boundedAboveProjectiveCondition k).ι
    let H := HomotopyCategory.quotient PST (ComplexShape.up ℤ)
    let Dq := DerivedCategory.Qh (C := PST)
    let d := HomologicalComplex.mapBifunctorSingleSingleIso B P Q n n
    V.map (derivedConvolutionSingleTensorIso P Q n).hom =
      Dq.map (U.map (singleProjectiveComparison P n ⊗ᵢ singleProjectiveComparison Q n).hom) ≫
        Dq.map (H.map d.hom) ≫ (DerivedCategory.quotientCompQhIso PST).hom.app _ := by
  intro V U H Dq d
  let p := singleProjectiveComparison P n
  let q := singleProjectiveComparison Q n
  let b : V.obj ((E).functor.obj (singleProjective P n ⊗ singleProjective Q n)) ≅
      V.obj ((singleDerivedMinus k (n + n)).obj (((B).obj P).obj Q)) :=
    Dq.mapIso (H.mapIso d) ≪≫
    (DerivedCategory.quotientCompQhIso PST).app
      ((CochainComplex.singleFunctor PST (n + n)).obj (((B).obj P).obj Q))
  let a := (E).functor.map (p ⊗ᵢ q).hom
  change V.map (a ≫ V.preimage b.hom) = V.map a ≫ _
  exact (V.map_comp a (V.preimage b.hom)).trans
    (congrArg (V.map a ≫ ·) (Functor.map_preimage V b.hom))

set_option maxHeartbeats 850000 in
-- Compose the original projective, quotient and cochain symmetry squares.
/-- In degree `n`, the derived tensor comparison carries the symmetry of two
projective singles to the coefficient symmetry with sign `(-1)^(n*n)`. -/
theorem derivedConvolutionSingle_braiding (P Q : PST) [Projective P] [Projective Q] (n : ℤ) :
    (β_ ((singleDerivedMinus k n).obj P) ((singleDerivedMinus k n).obj Q)).hom ≫
        (derivedConvolutionSingleTensorIso Q P n).hom =
      (n * n).negOnePow • ((derivedConvolutionSingleTensorIso P Q n).hom ≫
        (singleDerivedMinus k (n + n)).map (convolutionSwapHom F
          (BraidedCategory.curriedBraidingNatIso (Cor k)) P Q)) := by
  let U := (boundedAboveProjectiveCondition k).ι
  let V := DerivedCategory.Minus.ι (C := PST)
  let c := ComplexShape.up ℤ
  let H := HomotopyCategory.quotient PST c
  let Dq := DerivedCategory.Qh (C := PST)
  let C := (CochainComplex.singleFunctor PST n).obj P
  let C' := (CochainComplex.singleFunctor PST n).obj Q
  let d := HomologicalComplex.mapBifunctorSingleSingleIso B P Q n n
  let d' := HomologicalComplex.mapBifunctorSingleSingleIso B Q P n n
  let φ := (CochainComplex.singleFunctor PST (n + n)).map (convolutionSwapHom F
      (BraidedCategory.curriedBraidingNatIso (Cor k)) P Q)
  let p := singleProjectiveComparison P n
  let q := singleProjectiveComparison Q n
  let e := DerivedCategory.quotientCompQhIso PST
  apply V.map_injective
  simp only [V.map_comp, Functor.map_units_smul, derivedConvolution_braiding_map]
  rw [derivedConvolutionSingleTensorIso_map_hom Q P n,
    derivedConvolutionSingleTensorIso_map_hom P Q n]
  simp only [Category.assoc]
  change Dq.map (U.map (β_ _ _).hom) ≫ Dq.map (U.map (q ⊗ᵢ p).hom) ≫
      Dq.map (H.map d'.hom) ≫ e.hom.app _ =
    (n * n).negOnePow • (Dq.map (U.map (p ⊗ᵢ q).hom) ≫ Dq.map (H.map d.hom) ≫
      e.hom.app _ ≫ DerivedCategory.Q.map φ)
  let := convolutionCochainMonoidalCategory (k := k)
  let := convolutionCochainSymmetricCategory (k := k)
  let a := U.map (β_ ((E).inverse.obj ((singleDerivedMinus k n).obj P))
    ((E).inverse.obj ((singleDerivedMinus k n).obj Q))).hom
  let a' := U.map (q ⊗ᵢ p).hom
  let b := U.map (p ⊗ᵢ q).hom
  let b' := U.map (β_ (singleProjective P n) (singleProjective Q n)).hom
  let v := (β_ C C').hom
  have hab : a ≫ a' = b ≫ b' := by
    dsimp only [a, a', b, b']
    rw [← U.map_comp, ← U.map_comp, tensorIso_hom, tensorIso_hom]
    exact U.congr_map (BraidedCategory.braiding_naturality p.hom q.hom).symm
  have hβ : b' = H.map v := convolutionHomotopy_braiding_on_cochains C C'
  have h₁ : Dq.map a ≫ Dq.map a' = Dq.map b ≫ Dq.map (H.map v) :=
    ((Dq.map_comp a a').symm.trans (Dq.congr_map hab)).trans
      ((Dq.map_comp b b').trans (congrArg (fun t => Dq.map b ≫ Dq.map t) hβ))
  have hC : v ≫ d'.hom = (n * n).negOnePow • (d.hom ≫ φ) :=
    convolutionCochainSingle_braiding P Q n
  have h₂ : Dq.map (H.map v) ≫ Dq.map (H.map d'.hom) =
      (n * n).negOnePow • (Dq.map (H.map d.hom) ≫ Dq.map (H.map φ)) := by
    let L := H ⋙ Dq
    change L.map v ≫ L.map d'.hom = (n * n).negOnePow • (L.map d.hom ≫ L.map φ)
    rw [← L.map_comp, hC, Functor.map_units_smul, L.map_comp]
  have h₃ : Dq.map (H.map φ) ≫ e.hom.app _ = e.hom.app _ ≫ DerivedCategory.Q.map φ :=
    e.hom.naturality φ
  change Dq.map a ≫ Dq.map a' ≫ Dq.map (H.map d'.hom) ≫ e.hom.app _ = _
  rw [reassoc_of% h₁, reassoc_of% h₂, Linear.units_smul_comp, Linear.comp_units_smul,
    Category.assoc]
  exact congrArg (fun t => (n * n).negOnePow • (Dq.map b ≫ Dq.map (H.map d.hom) ≫ t)) h₃

set_option maxHeartbeats 850000 in
-- Keep the monoidal quotient and coefficient-map comparisons explicit.
/-- The signed total of two projective singles preserves their original coefficient maps. -/
theorem derivedConvolutionSingle_naturality
    {P P' Q Q' : PST} [Projective P] [Projective P'] [Projective Q] [Projective Q']
    (f : P ⟶ P') (g : Q ⟶ Q') (n : ℤ) :
    let S := singleDerivedMinus k n
    (S.map f ⊗ₘ S.map g) ≫ (derivedConvolutionSingleTensorIso P' Q' n).hom =
      (derivedConvolutionSingleTensorIso P Q n).hom ≫
        (singleDerivedMinus k (n + n)).map (convolutionMap F f g) := by
  intro S
  let U := (boundedAboveProjectiveCondition k).ι
  let V := DerivedCategory.Minus.ι (C := PST)
  let c := ComplexShape.up ℤ
  let H := HomotopyCategory.quotient PST c
  let Dq := DerivedCategory.Qh (C := PST)
  let C := CochainComplex.singleFunctor PST n
  let d := HomologicalComplex.mapBifunctorSingleSingleIso B P Q n n
  let d' := HomologicalComplex.mapBifunctorSingleSingleIso B P' Q' n n
  let m := (CochainComplex.singleFunctor PST (n + n)).map (convolutionMap F f g)
  let p := singleProjectiveComparison P n
  let p' := singleProjectiveComparison P' n
  let q := singleProjectiveComparison Q n
  let q' := singleProjectiveComparison Q' n
  let E₀ := DerivedCategory.quotientCompQhIso PST
  let f₀ : singleProjective P n ⟶ singleProjective P' n :=
    ObjectProperty.homMk (H.map (C.map f))
  let g₀ : singleProjective Q n ⟶ singleProjective Q' n :=
    ObjectProperty.homMk (H.map (C.map g))
  have h₁ : (E).inverse.map (S.map f) ≫ p'.hom = p.hom ≫ f₀ :=
    singleProjectiveComparison_naturality f n
  have h₂ : (E).inverse.map (S.map g) ≫ q'.hom = q.hom ≫ g₀ :=
    singleProjectiveComparison_naturality g n
  have h := convolutionCochainSingle_naturality f g n
  apply V.map_injective
  simp only [V.map_comp]
  rw [derivedConvolutionSingleTensorIso_map_hom P' Q' n,
    derivedConvolutionSingleTensorIso_map_hom P Q n]
  change Dq.map (U.map ((E).inverse.map (S.map f) ⊗ₘ (E).inverse.map (S.map g))) ≫
      Dq.map (U.map (p'.hom ⊗ₘ q'.hom)) ≫ Dq.map (H.map d'.hom) ≫ E₀.hom.app _ =
    (Dq.map (U.map (p.hom ⊗ₘ q.hom)) ≫ Dq.map (H.map d.hom) ≫ E₀.hom.app _) ≫
      DerivedCategory.Q.map m
  let := convolutionCochainMonoidalCategory (k := k)
  let := convolutionCochainSymmetricCategory (k := k)
  let := convolutionHomotopyQuotientMonoidal (k := k)
  let a := U.map ((E).inverse.map (S.map f) ⊗ₘ (E).inverse.map (S.map g))
  let a' := U.map (p'.hom ⊗ₘ q'.hom)
  let b := U.map (p.hom ⊗ₘ q.hom)
  let b' := U.map (f₀ ⊗ₘ g₀)
  let v := C.map f ⊗ₘ C.map g
  have hab : a ≫ a' = b ≫ b' := by
    dsimp only [a, a', b, b']
    rw [← U.map_comp, ← U.map_comp, tensorHom_comp_tensorHom, h₁, h₂,
      ← tensorHom_comp_tensorHom]
  have hT : b' = H.map v := by
    have hμ := Functor.LaxMonoidal.μ_natural H (C.map f) (C.map g)
    rw [convolutionHomotopyQuotientMonoidal_μ (C.obj P') (C.obj Q'),
      convolutionHomotopyQuotientMonoidal_μ (C.obj P) (C.obj Q),
      Category.comp_id, Category.id_comp] at hμ
    exact hμ
  have hA : Dq.map a ≫ Dq.map a' = Dq.map b ≫ Dq.map (H.map v) :=
    ((Dq.map_comp a a').symm.trans (Dq.congr_map hab)).trans
      ((Dq.map_comp b b').trans (congrArg (fun t => Dq.map b ≫ Dq.map t) hT))
  have hC : v ≫ d'.hom = d.hom ≫ m := h
  have hB : Dq.map (H.map v) ≫ Dq.map (H.map d'.hom) =
      Dq.map (H.map d.hom) ≫ Dq.map (H.map m) := by
    let L := H ⋙ Dq
    change L.map v ≫ L.map d'.hom = L.map d.hom ≫ L.map m
    rw [← L.map_comp, hC, L.map_comp]
  have hE : Dq.map (H.map m) ≫ E₀.hom.app _ = E₀.hom.app _ ≫ DerivedCategory.Q.map m :=
    E₀.hom.naturality m
  change Dq.map a ≫ Dq.map a' ≫ Dq.map (H.map d'.hom) ≫ E₀.hom.app _ = _
  rw [reassoc_of% hA, reassoc_of% hB]
  change Dq.map b ≫ Dq.map (H.map d.hom) ≫
      (Dq.map (H.map m) ≫ E₀.hom.app _) =
    (Dq.map b ≫ Dq.map (H.map d.hom) ≫ E₀.hom.app _) ≫ DerivedCategory.Q.map m
  exact (congrArg (fun t => Dq.map b ≫ Dq.map (H.map d.hom) ≫ t) hE).trans
    ((Category.assoc _ _ _).trans (congrArg (Dq.map b ≫ ·) (Category.assoc _ _ _))).symm

end AlgebraicGeometry.PresheafWithTransfers
