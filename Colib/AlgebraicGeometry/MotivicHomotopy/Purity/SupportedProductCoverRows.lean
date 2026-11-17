/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.SupportedProductCoverComparison
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.CoverComparison
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.TransferExcision
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.SignedExactness
public import Colib.CategoryTheory.Square.ShortComplex

/-! # Signed coefficient rows on the actual cover and product-pair squares -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry.Scheme
open SmoothSite.Contraction

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

section SignedRows

variable {S C N D : Type*} [Category* S] [Category* C] [Category* N] [Category* D]
  [Preadditive C] [Preadditive N] [Preadditive D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts N] [HasBinaryBiproducts D]
  (F : C ⥤ D) (G : N ⥤ D) [F.Additive] [G.Additive]
  [PreservesBinaryBiproducts F] [PreservesBinaryBiproducts G]
  {J : S ⥤ C} {K : S ⥤ N} (a : J ⋙ F ≅ K ⋙ G) (sq : Square S)

/-- Identify signed rows along their corner comparison and the coefficient-square equality. -/
def signedSquareRowCompositeIso (Q : Square N) (h : sq.map K = Q) :
    ((sq.map J).commSq.shortComplex.map F) ≅ (Q.commSq.shortComplex.map G) :=
  h ▸ (mapSignedSquareRowIso F a sq ≪≫
    (mapSignedSquareRowIso G (Iso.refl (K ⋙ G)) sq).symm)

private theorem signedSquareRowProjection_fst :
    (mapSignedSquareRowIso F a sq ≪≫
        (mapSignedSquareRowIso G (Iso.refl (K ⋙ G)) sq).symm).hom.τ₂ ≫
        G.map (biprod.fst : K.obj sq.X₂ ⊞ K.obj sq.X₃ ⟶ _) =
      F.map (biprod.fst : J.obj sq.X₂ ⊞ J.obj sq.X₃ ⟶ _) ≫ a.hom.app sq.X₂ := by
  simp [mapSignedSquareRowIso, Category.assoc, ← Functor.map_comp]

private theorem signedSquareRowProjection_snd :
    (mapSignedSquareRowIso F a sq ≪≫
        (mapSignedSquareRowIso G (Iso.refl (K ⋙ G)) sq).symm).hom.τ₂ ≫
        G.map (biprod.snd : K.obj sq.X₂ ⊞ K.obj sq.X₃ ⟶ _) =
      F.map (biprod.snd : J.obj sq.X₂ ⊞ J.obj sq.X₃ ⟶ _) ≫ a.hom.app sq.X₃ := by
  simp [mapSignedSquareRowIso, Category.assoc, ← Functor.map_comp]

end SignedRows

section MappedSignedRows

variable {S C B N D : Type*} [Category* S] [Category* C] [Category* B] [Category* N] [Category* D]
  [Preadditive C] [Preadditive N] [Preadditive D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts N] [HasBinaryBiproducts D]
  (F : C ⥤ D) (G : N ⥤ D) [F.Additive] [G.Additive]
  [PreservesBinaryBiproducts F] [PreservesBinaryBiproducts G]
  (Q : B ⥤ N) {J : S ⥤ C} {K : S ⥤ B} (a : J ⋙ F ≅ (K ⋙ Q) ⋙ G) (sq : Square S)
  {A : Square B} (h : sq.map K = A)

set_option quotPrecheck false in
local notation "baseRowIso" =>
  (mapSignedSquareRowIso F a sq ≪≫ (mapSignedSquareRowIso G (Iso.refl ((K ⋙ Q) ⋙ G)) sq).symm)

/-- Compare the coefficient rows along an equality of their underlying squares. -/
def signedSquareRowIsoOfMappedSquareEq :
    (sq.map J).commSq.shortComplex.map F ≅ (A.map Q).commSq.shortComplex.map G :=
  Square.compMapShortComplexIso (A := sq.map K) Q G baseRowIso h

private theorem signedSquareRowIsoOfMappedSquareEq_hom₁ :
    (signedSquareRowIsoOfMappedSquareEq F G Q a sq h).hom.τ₁ =
      a.hom.app sq.X₁ ≫ (Q ⋙ G).map (eqToHom (congrArg (fun A : Square B => A.X₁) h)) :=
  (Square.compMapShortComplexIso_hom₁ (A := sq.map K) Q G baseRowIso h).trans
    (congrArg (· ≫ (Q ⋙ G).map (eqToHom (congrArg (fun A : Square B => A.X₁) h)))
      (Category.comp_id (a.hom.app sq.X₁)))

private theorem signedSquareRowIsoOfMappedSquareEq_hom₃ :
    (signedSquareRowIsoOfMappedSquareEq F G Q a sq h).hom.τ₃ =
      a.hom.app sq.X₄ ≫ (Q ⋙ G).map (eqToHom (congrArg (fun A : Square B => A.X₄) h)) :=
  (Square.compMapShortComplexIso_hom₃ (A := sq.map K) Q G baseRowIso h).trans
    (congrArg (· ≫ (Q ⋙ G).map (eqToHom (congrArg (fun A : Square B => A.X₄) h)))
      (Category.comp_id (a.hom.app sq.X₄)))

private theorem signedSquareRowIsoOfMappedSquareEq_fst :
    (signedSquareRowIsoOfMappedSquareEq F G Q a sq h).hom.τ₂ ≫
        G.map (biprod.fst : Q.obj A.X₂ ⊞ Q.obj A.X₃ ⟶ Q.obj A.X₂) =
      F.map (biprod.fst : J.obj sq.X₂ ⊞ J.obj sq.X₃ ⟶ J.obj sq.X₂) ≫
        a.hom.app sq.X₂ ≫ (Q ⋙ G).map (eqToHom (congrArg (fun A : Square B => A.X₂) h)) :=
  (Square.compMapShortComplexIso_fst (A := sq.map K) Q G baseRowIso h).trans
    ((congrArg (· ≫ (Q ⋙ G).map (eqToHom (congrArg (fun A : Square B => A.X₂) h)))
      (signedSquareRowProjection_fst (K := K ⋙ Q) F G a sq)).trans (Category.assoc _ _ _))

private theorem signedSquareRowIsoOfMappedSquareEq_snd :
    (signedSquareRowIsoOfMappedSquareEq F G Q a sq h).hom.τ₂ ≫
        G.map (biprod.snd : Q.obj A.X₂ ⊞ Q.obj A.X₃ ⟶ Q.obj A.X₃) =
      F.map (biprod.snd : J.obj sq.X₂ ⊞ J.obj sq.X₃ ⟶ J.obj sq.X₃) ≫
        a.hom.app sq.X₃ ≫ (Q ⋙ G).map (eqToHom (congrArg (fun A : Square B => A.X₃) h)) :=
  (Square.compMapShortComplexIso_snd (A := sq.map K) Q G baseRowIso h).trans
    ((congrArg (· ≫ (Q ⋙ G).map (eqToHom (congrArg (fun A : Square B => A.X₃) h)))
      (signedSquareRowProjection_snd (K := K ⋙ Q) F G a sq)).trans (Category.assoc _ _ _))

end MappedSignedRows

private theorem squareMap_comp {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (sq : Square C) (F : C ⥤ D) (G : D ⥤ E) :
    sq.map (F ⋙ G) = (sq.map F).map G := (rfl)

variable (k : Type u) [Field k]

attribute [local instance] productCoverComparisonCorSheafify
  productCoverComparisonSmoothSheafify productCoverComparisonAbelian

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

local notation "Sm(" K ")" => SmoothSite (Spec (CommRingCat.of K))
local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
set_option quotPrecheck false in
local notation "D" => DerivedCategory.Minus PST
local notation "s" => singleTransferSheafMinus k
local notation "sₚ" => singleDerivedMinus k 0
local notation "A" => derivedNisnevichSheafification k
local notation "γ" => Cor.graphFunctor k
set_option quotPrecheck false in
local notation "Rₚ" => γ ⋙ representableLarge k
local notation "R₁" => smoothTransferRepresentable k
set_option quotPrecheck false in
local notation "R₀" => Rₚ ⋙ sₚ

attribute [local instance] derivedConvolutionMonoidalCategory derivedConvolutionCommShift₂Int

/-- The signed derived left tensor is additive in its right variable. -/
local instance supportedProductDerivedTensorAdditive (K : D) : (tensorLeft K).Additive := by
  let : (tensorLeft K).IsTriangulated := derivedSignedTensorLeft_isTriangulated K
  infer_instance

/-- Exact sheafification of the literal presheaf single. -/
abbrev derivedSheafificationSingleIso (N : PST) :
    (A).obj ((sₚ).obj N) ≅ (s).obj ((nisnevichSheafify k).obj N) :=
  (Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.Minus.ι (C := NST))).preimageIso
    (((nisnevichSheafify k).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor PST (0 : ℤ)).obj N)) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex (nisnevichSheafify k)
          (ComplexShape.up ℤ) (0 : ℤ)).app N))

/-- Derived sheafification of the literal projective representable is its original sheaf. -/
def derivedMotiveRepresentableIso : R₀ ⋙ A ≅ R₁ ⋙ s :=
  NatIso.ofComponents (fun X => derivedSheafificationSingleIso k ((Rₚ).obj X)) (by
    intro X Y f
    apply (DerivedCategory.Minus.ι (C := NST)).map_injective
    simp only [Functor.map_comp, derivedSheafificationSingleIso, Functor.FullyFaithful.preimageIso,
      Functor.FullyFaithful.map_preimage, Iso.trans_hom, Functor.mapIso_hom]
    let G := nisnevichSheafify k
    let c := ComplexShape.up ℤ
    let e := G.mapDerivedCategoryFactors
    let ε := HomologicalComplex.singleMapHomologicalComplex G c (0 : ℤ)
    let a := (Rₚ).map f
    let g := (CochainComplex.singleFunctor PST 0).map a
    let h := (CochainComplex.singleFunctor NST 0).map (G.map a)
    change G.mapDerivedCategory.map (DerivedCategory.Q.map g) ≫
        e.hom.app _ ≫ DerivedCategory.Q.map (ε.hom.app ((Rₚ).obj Y)) =
      (e.hom.app _ ≫ DerivedCategory.Q.map (ε.hom.app ((Rₚ).obj X))) ≫
        DerivedCategory.Q.map h
    rw [G.mapDerivedCategoryFactors_hom_naturality_assoc g, Category.assoc,
      ← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
    exact congrArg (fun z => e.hom.app _ ≫ DerivedCategory.Q.map z) (ε.hom.naturality a))

variable {U V : Sm(k)} (j : U ⟶ V) [IsOpenImmersion j.left]

set_option quotPrecheck false in
local notation "P" => (projectivePairDerived k).obj (Arrow.mk j)
set_option quotPrecheck false in
local notation "F" => tensorLeft P ⋙ A

/-- The signed row on the original represented cover. -/
abbrev representedCoverRow (sq : Square Sm(k)) : ShortComplex D :=
  (sq.map (R₀)).commSq.shortComplex

/-- The original signed quotient row of the product pairs over the cover. -/
abbrev productCoverRow (sq : Square Sm(k)) :=
  transferPairOpenCoverSequence k (smoothPairProductCoverMap j sq)

/-- Derived sheafification preserves the two chart summands of the cover. -/
local instance derivedSheafification_preservesBinaryBiproducts :
    PreservesBinaryBiproducts A := by
  let : (A).IsTriangulated := nisnevichDerivedMinus_isTriangulated k
  exact preservesBinaryBiproducts_of_preservesBiproducts _

/-- Tensoring with the relative motive and sheafifying preserves binary sums. -/
local instance relativeDerivedProduct_preservesBinaryBiproducts :
    PreservesBinaryBiproducts F := by
  let : (A).IsTriangulated := nisnevichDerivedMinus_isTriangulated k
  let : (tensorLeft P).IsTriangulated := derivedSignedTensorLeft_isTriangulated P
  exact preservesBinaryBiproducts_of_preservesBiproducts _

/-- Transfer sheaves placed in degree zero preserve binary sums. -/
local instance singleTransferSheafMinus_preservesBinaryBiproducts :
    PreservesBinaryBiproducts s :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/-- Exact sheafification identifies the represented row with the literal transfer row. -/
def ordinaryCoverRowIso (sq : Square Sm(k)) :
    (representedCoverRow k sq).map A ≅ (transferMayerVietorisSequence k sq).map s :=
  mapSignedSquareRowIso A (derivedMotiveRepresentableIso k) sq ≪≫
    (mapSignedSquareRowIso s (Iso.refl (R₁ ⋙ s)) sq).symm

/-- The first projection of the ordinary row comparison is the represented chart map. -/
theorem ordinaryCoverRowIso_hom₂_fst (sq : Square Sm(k)) :
    (ordinaryCoverRowIso k sq).hom.τ₂ ≫
        (s).map (biprod.fst : (R₁).obj sq.X₂ ⊞ (R₁).obj sq.X₃ ⟶ _) =
      (A).map (biprod.fst : (R₀).obj sq.X₂ ⊞ (R₀).obj sq.X₃ ⟶ _) ≫
        (derivedMotiveRepresentableIso k).hom.app sq.X₂ := by
  unfold ordinaryCoverRowIso
  exact signedSquareRowProjection_fst A s (derivedMotiveRepresentableIso k) sq

/-- The second projection of the ordinary row comparison is the represented chart map. -/
theorem ordinaryCoverRowIso_hom₂_snd (sq : Square Sm(k)) :
    (ordinaryCoverRowIso k sq).hom.τ₂ ≫
        (s).map (biprod.snd : (R₁).obj sq.X₂ ⊞ (R₁).obj sq.X₃ ⟶ _) =
      (A).map (biprod.snd : (R₀).obj sq.X₂ ⊞ (R₀).obj sq.X₃ ⟶ _) ≫
        (derivedMotiveRepresentableIso k).hom.app sq.X₃ := by
  unfold ordinaryCoverRowIso
  exact signedSquareRowProjection_snd A s (derivedMotiveRepresentableIso k) sq

omit [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)] [IsOpenImmersion j.left] in
/-- The four product pairs and their comparison maps form the image of the cover square. -/
theorem pairProductParameter_square (sq : Square Sm(k)) :
    sq.map (pairProductParameter k j) = arrowSquare (smoothPairProductCoverMap j sq) := (rfl)

set_option maxHeartbeats 750000 in
-- Map the arrow-square equality using the generic composition of square maps.
omit [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)] [IsOpenImmersion j.left] in
/-- Mapping the product square by the quotient functor gives the original
square of relative transfer quotients. -/
theorem pairProductQuotientSquare_eq (sq : Square Sm(k)) :
    sq.map (pairProductParameter k j ⋙ transferPairCokernelFunctor k) =
      transferPairOpenCoverSquare k (smoothPairProductCoverMap j sq) := by
  let Q := transferPairCokernelFunctor k
  unfold transferPairOpenCoverSquare
  exact (squareMap_comp sq (pairProductParameter k j) Q).trans
    (congrArg (fun a : Square (Arrow Sm(k)) => a.map Q) (pairProductParameter_square k j sq))

/-- The literal square of product-pair quotients over the cover. -/
abbrev productCoverQuotientSquare (sq : Square Sm(k)) :=
  transferPairOpenCoverSquare k (smoothPairProductCoverMap j sq)

set_option quotPrecheck false in
local notation "Qₚ(" sq ")" => productCoverQuotientSquare k j sq

set_option quotPrecheck false in
local notation "QF" => pairProductParameter k j ⋙ transferPairCokernelFunctor k

/-- The original product-pair comparison with the coefficient functors grouped for the rows. -/
abbrev pairCoverCoefficientComparison : R₀ ⋙ F ≅ QF ⋙ s :=
  derivedProductPairEndNatIso k j

attribute [local irreducible] signedSquareRowIsoOfMappedSquareEq

set_option maxHeartbeats 950000 in
-- The parameter squares are compared before taking transfer quotients.
/-- The derived tensor row identifies with the degree-zero row of literal product-pair quotients. -/
abbrev pairCoverRowIso (sq : Square Sm(k)) :
    (representedCoverRow k sq).map F ≅ (productCoverRow k j sq).map s :=
  signedSquareRowIsoOfMappedSquareEq (J := R₀) (K := pairProductParameter k j)
    F s (transferPairCokernelFunctor k) (pairCoverCoefficientComparison k j) sq
    (pairProductParameter_square k j sq)

attribute [local irreducible] Cor.graphFunctor SheafWithTransfers.transferRepresentable
set_option backward.isDefEq.respectTransparency true

set_option maxHeartbeats 750000 in
/-- The overlap component of the derived row is the original augmentation comparison. -/
theorem pairCoverRowIso_hom₁ (sq : Square Sm(k)) :
    (pairCoverRowIso k j sq).hom.τ₁ = (derivedProductPairEndIso k j sq.X₁).hom := by
  let Q := transferPairCokernelFunctor k
  let e := pairProductParameter_square k j sq
  let a := pairCoverCoefficientComparison k j
  let v := a.hom.app sq.X₁
  let c := eqToHom (congrArg (fun T : Square (Arrow Sm(k)) => T.X₁) e)
  have hc : c = 𝟙 ((pairProductParameter k j).obj sq.X₁) := (rfl)
  have h := signedSquareRowIsoOfMappedSquareEq_hom₁
    (J := R₀) (K := pairProductParameter k j) F s Q a sq e
  have hId : (Q ⋙ s).map c = 𝟙 _ :=
    ((Q ⋙ s).congr_map hc).trans ((Q ⋙ s).map_id _)
  exact h.trans ((congrArg (v ≫ ·) hId).trans
    ((Category.comp_id v).trans (derivedProductPairEndNatIso_hom_app k j sq.X₁)))

set_option maxHeartbeats 750000 in
/-- The union component of the derived row is the original augmentation comparison. -/
theorem pairCoverRowIso_hom₃ (sq : Square Sm(k)) :
    (pairCoverRowIso k j sq).hom.τ₃ = (derivedProductPairEndIso k j sq.X₄).hom := by
  let Q := transferPairCokernelFunctor k
  let e := pairProductParameter_square k j sq
  let a := pairCoverCoefficientComparison k j
  let v := a.hom.app sq.X₄
  let c := eqToHom (congrArg (fun T : Square (Arrow Sm(k)) => T.X₄) e)
  have hc : c = 𝟙 ((pairProductParameter k j).obj sq.X₄) := (rfl)
  have h := signedSquareRowIsoOfMappedSquareEq_hom₃
    (J := R₀) (K := pairProductParameter k j) F s Q a sq e
  have hId : (Q ⋙ s).map c = 𝟙 _ :=
    ((Q ⋙ s).congr_map hc).trans ((Q ⋙ s).map_id _)
  exact h.trans ((congrArg (v ≫ ·) hId).trans
    ((Category.comp_id v).trans (derivedProductPairEndNatIso_hom_app k j sq.X₄)))

set_option maxHeartbeats 750000 in
/-- The first projection of the product row is the original pair comparison on that chart. -/
theorem pairCoverRowIso_hom₂_fst (sq : Square Sm(k)) :
    (pairCoverRowIso k j sq).hom.τ₂ ≫
        (s).map (biprod.fst : Qₚ(sq).X₂ ⊞ Qₚ(sq).X₃ ⟶ _) =
      (F).map (biprod.fst : (R₀).obj sq.X₂ ⊞ (R₀).obj sq.X₃ ⟶ _) ≫
        (derivedProductPairEndIso k j sq.X₂).hom := by
  let Q := transferPairCokernelFunctor k
  let e := pairProductParameter_square k j sq
  let a := pairCoverCoefficientComparison k j
  let v := a.hom.app sq.X₂
  let m := (F).map (biprod.fst : (R₀).obj sq.X₂ ⊞ (R₀).obj sq.X₃ ⟶ _)
  let c := eqToHom (congrArg (fun T : Square (Arrow Sm(k)) => T.X₂) e)
  have hc : c = 𝟙 ((pairProductParameter k j).obj sq.X₂) := (rfl)
  have h := signedSquareRowIsoOfMappedSquareEq_fst
    (J := R₀) (K := pairProductParameter k j) F s Q a sq e
  have hId : (Q ⋙ s).map c = 𝟙 _ :=
    ((Q ⋙ s).congr_map hc).trans ((Q ⋙ s).map_id _)
  exact h.trans (congrArg (m ≫ ·) ((congrArg (v ≫ ·) hId).trans
    ((Category.comp_id v).trans (derivedProductPairEndNatIso_hom_app k j sq.X₂))))

set_option maxHeartbeats 750000 in
/-- The second projection of the product row is the original pair comparison on that chart. -/
theorem pairCoverRowIso_hom₂_snd (sq : Square Sm(k)) :
    (pairCoverRowIso k j sq).hom.τ₂ ≫
        (s).map (biprod.snd : Qₚ(sq).X₂ ⊞ Qₚ(sq).X₃ ⟶ _) =
      (F).map (biprod.snd : (R₀).obj sq.X₂ ⊞ (R₀).obj sq.X₃ ⟶ _) ≫
        (derivedProductPairEndIso k j sq.X₃).hom := by
  let Q := transferPairCokernelFunctor k
  let e := pairProductParameter_square k j sq
  let a := pairCoverCoefficientComparison k j
  let v := a.hom.app sq.X₃
  let m := (F).map (biprod.snd : (R₀).obj sq.X₂ ⊞ (R₀).obj sq.X₃ ⟶ _)
  let c := eqToHom (congrArg (fun T : Square (Arrow Sm(k)) => T.X₃) e)
  have hc : c = 𝟙 ((pairProductParameter k j).obj sq.X₃) := (rfl)
  have h := signedSquareRowIsoOfMappedSquareEq_snd
    (J := R₀) (K := pairProductParameter k j) F s Q a sq e
  have hId : (Q ⋙ s).map c = 𝟙 _ :=
    ((Q ⋙ s).congr_map hc).trans ((Q ⋙ s).map_id _)
  exact h.trans (congrArg (m ≫ ·) ((congrArg (v ≫ ·) hId).trans
    ((Category.comp_id v).trans (derivedProductPairEndNatIso_hom_app k j sq.X₃))))

end AlgebraicGeometry.MotivicHomotopy
