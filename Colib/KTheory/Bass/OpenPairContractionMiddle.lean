/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.OpenPairProductTransport
public import Colib.KTheory.Bass.TwoChartMiddleBiproduct
public import Colib.KTheory.Bass.TwoChartAdditive
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Interchanging contraction with the original open-pair Bass middle row

The actual independent polynomial and Laurent product swaps identify contraction of the
original pair common-corner and signed chart-difference row with the same row of the contracted
functor. The comparison preserves both original chart maps and the original projection. It
asserts no exactness for an arbitrary row and identifies no boundary with a quotient projection.

Source: `Quillen/KTheory/Bass/OpenPairContractionMiddle.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme
universe u w
namespace AlgebraicGeometry.Scheme.Bass
open KTheory.Bass.TwoChart

section

variable (F : QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})

/-- The unchanged common projection and signed chart difference as a natural short complex. -/
def pairBassMiddleComplex : ShortComplex (QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :=
  ShortComplex.mk
    (biprod.lift (Functor.whiskerRight (NatTrans.op pairPolynomialProjection) F)
      (Functor.whiskerRight (NatTrans.op pairPolynomialProjection) F))
    (biprod.desc (Functor.whiskerRight (NatTrans.op pairPlus) F)
      (-Functor.whiskerRight (NatTrans.op pairMinus) F)) (by
    rw [biprod.lift_desc, Preadditive.comp_neg]
    have h : Functor.whiskerRight (NatTrans.op pairPolynomialProjection) F ≫
        Functor.whiskerRight (NatTrans.op pairPlus) F =
      Functor.whiskerRight (NatTrans.op pairPolynomialProjection) F ≫
        Functor.whiskerRight (NatTrans.op pairMinus) F := by
      apply NatTrans.ext
      funext X
      change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
      rw [← F.map_comp, ← F.map_comp]
      apply congrArg F.map
      apply Quiver.Hom.unop_inj
      exact (pairPlus_projection X.unop).trans (pairMinus_projection X.unop).symm
    rw [h, add_neg_cancel])

/-- The genuine product transport preserves the original positive chart after contraction. -/
@[reassoc]
theorem pairProductContractionTransportIso_plus :
    (contractionFunctor (NatTrans.op pairPlus) (NatTrans.op pairMinus)).map
        (Functor.whiskerRight (NatTrans.op pairPlus) F) ≫
      (pairProductContractionTransportIso
        (PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u} ℤ))) F).hom =
    (pairProductContractionTransportIso
      (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ))) F).hom ≫
        Functor.whiskerRight (NatTrans.op pairPlus)
          (contraction (NatTrans.op pairPlus) (NatTrans.op pairMinus) F) := by
  apply NatTrans.ext
  funext X
  exact pairProductContractionTransportIso_factorMap
    (PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u} ℤ)))
    (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ)))
    (PolynomialLaurent.laurentToPolynomial (CommRingCat.of (ULift.{u} ℤ)))
    (PolynomialLaurent.laurentToPolynomial_projection (CommRingCat.of (ULift.{u} ℤ))) F X

/-- The same product transport retains the original inverse-coordinate chart. -/
@[reassoc]
theorem pairProductContractionTransportIso_minus :
    (contractionFunctor (NatTrans.op pairPlus) (NatTrans.op pairMinus)).map
        (Functor.whiskerRight (NatTrans.op pairMinus) F) ≫
      (pairProductContractionTransportIso
        (PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u} ℤ))) F).hom =
    (pairProductContractionTransportIso
      (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ))) F).hom ≫
        Functor.whiskerRight (NatTrans.op pairMinus)
          (contraction (NatTrans.op pairPlus) (NatTrans.op pairMinus) F) := by
  apply NatTrans.ext
  funext X
  exact pairProductContractionTransportIso_factorMap
    (PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u} ℤ)))
    (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ)))
    (PolynomialLaurent.laurentMinus (CommRingCat.of (ULift.{u} ℤ)))
    (PolynomialLaurent.laurentMinus_projection (CommRingCat.of (ULift.{u} ℤ))) F X

/-- Actual independent-variable interchange on all three objects and both original middle maps.
-/
def pairContractionBassMiddleIso :
    (pairBassMiddleComplex F).map
        (contractionFunctor (NatTrans.op pairPlus) (NatTrans.op pairMinus)) ≅
      pairBassMiddleComplex (contraction (NatTrans.op pairPlus) (NatTrans.op pairMinus) F) := by
  let B := contractionFunctor (NatTrans.op pairPlus) (NatTrans.op pairMinus)
  let : PreservesBinaryBiproducts B := preservesBinaryBiproducts_of_preservesBinaryProducts B
  let eP : B.obj (pairPolynomialFunctor.op ⋙ F) ≅ pairPolynomialFunctor.op ⋙ B.obj F :=
    pairProductContractionTransportIso
    (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ))) F
  let eL : B.obj (pairLaurentFunctor.op ⋙ F) ≅ pairLaurentFunctor.op ⋙ B.obj F :=
    pairProductContractionTransportIso
    (PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u} ℤ))) F
  let c := Functor.whiskerRight (NatTrans.op pairPolynomialProjection) F
  let p := Functor.whiskerRight (NatTrans.op pairPlus) F
  let m := Functor.whiskerRight (NatTrans.op pairMinus) F
  have hc : B.map c ≫ eP.hom =
      Functor.whiskerRight (NatTrans.op pairPolynomialProjection) (B.obj F) := by
    apply NatTrans.ext
    funext X
    exact pairProductContractionTransportIso_polynomialProjection F X
  refine ShortComplex.isoMk (Iso.refl _)
    ((B.mapBiprod (pairPolynomialFunctor.op ⋙ F) (pairPolynomialFunctor.op ⋙ F)) ≪≫
      biprod.mapIso eP eP) eL ?_ ?_
  · change 𝟙 _ ≫ biprod.lift _ _ =
      B.map (biprod.lift c c) ≫ (B.mapBiprod _ _).hom ≫ biprod.map eP.hom eP.hom
    rw [Category.id_comp, ← Category.assoc, biprod.map_lift_mapBiprod]
    apply biprod.hom_ext <;>
      simp only [Category.assoc, biprod.map_fst, biprod.map_snd,
        biprod.lift_fst, biprod.lift_snd, biprod.lift_fst_assoc,
        biprod.lift_snd_assoc, hc] <;> rfl
  · change ((B.mapBiprod _ _).hom ≫ biprod.map eP.hom eP.hom) ≫
        biprod.desc _ _ = B.map (biprod.desc p (-m)) ≫ eL.hom
    apply (cancel_epi (B.mapBiprod (pairPolynomialFunctor.op ⋙ F)
      (pairPolynomialFunctor.op ⋙ F)).inv).mp
    rw [← Category.assoc, ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
      ← Category.assoc, biprod.mapBiprod_inv_map_desc, Functor.map_neg]
    apply biprod.hom_ext'
    · simpa only [Category.assoc, biprod.inl_map_assoc, biprod.inl_desc_assoc,
        biprod.inl_desc] using (pairProductContractionTransportIso_plus F).symm
    · simpa only [Category.assoc, biprod.inr_map_assoc, biprod.inr_desc_assoc,
        biprod.inr_desc, Preadditive.comp_neg, Preadditive.neg_comp] using
        congrArg Neg.neg (pairProductContractionTransportIso_minus F).symm

end

/-- The two original charts coincide on the literal coefficient projection. -/
theorem pairCommonCorner :
    NatTrans.op pairPolynomialProjection ≫ NatTrans.op pairPlus =
      NatTrans.op pairPolynomialProjection ≫ NatTrans.op pairMinus := by
  apply NatTrans.ext
  funext X
  apply Quiver.Hom.unop_inj
  exact (pairPlus_projection X.unop).trans (pairMinus_projection X.unop).symm

/-- The actual pointwise Bass row is the original natural open-pair row. -/
def pairBassMiddlePointwiseIso
    (F : QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    middleComplex (NatTrans.op pairPolynomialProjection) (NatTrans.op pairPlus)
      (NatTrans.op pairMinus) pairCommonCorner F ≅ pairBassMiddleComplex F :=
  by
  let e := polynomialPairBiprodIso (NatTrans.op pairPlus) (NatTrans.op pairMinus) F
  refine ShortComplex.isoMk (Iso.refl F) e (Iso.refl (pairLaurentFunctor.op ⋙ F)) ?_ ?_
  · change 𝟙 F ≫ biprod.lift _ _ =
      middleCorner (NatTrans.op pairPolynomialProjection) (NatTrans.op pairPlus)
        (NatTrans.op pairMinus) F ≫ e.hom
    rw [Category.id_comp]
    apply biprod.hom_ext
    · rw [biprod.lift_fst, Category.assoc, polynomialPairBiprodIso_hom_fst]
      apply NatTrans.ext
      funext X
      exact (biprod.lift_fst _ _).symm
    · rw [biprod.lift_snd, Category.assoc, polynomialPairBiprodIso_hom_snd]
      apply NatTrans.ext
      funext X
      exact (biprod.lift_snd _ _).symm
  · change e.hom ≫ biprod.desc _ _ =
      middleDifference (NatTrans.op pairPlus) (NatTrans.op pairMinus) F ≫ 𝟙 _
    rw [Category.comp_id]
    apply (cancel_epi e.inv).mp
    rw [Iso.inv_hom_id_assoc]
    change biprod.desc _ _ = biprod.desc _ _ ≫
      middleDifference (NatTrans.op pairPlus) (NatTrans.op pairMinus) F
    apply biprod.hom_ext'
    · rw [biprod.inl_desc, biprod.inl_desc_assoc]
      apply NatTrans.ext
      funext X
      exact (biprod.inl_desc _ _).symm
    · rw [biprod.inr_desc, biprod.inr_desc_assoc]
      apply NatTrans.ext
      funext X
      exact (biprod.inr_desc _ _).symm

end AlgebraicGeometry.Scheme.Bass
