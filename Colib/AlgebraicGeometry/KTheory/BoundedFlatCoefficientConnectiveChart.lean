/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientConnectiveGroups
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientTwoChartStableSequence
public import Colib.AlgebraicGeometry.ProjectiveLine.CoefficientPolynomialLaurentCoordinates
public import Colib.AlgebraicGeometry.ProjectiveLine.PositiveBassChartComplex

/-! # The original connective chart complex on a native coefficient fiber -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.BaseChange.Coefficients AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.PolynomialLaurent CommRingCat.PolynomialLaurent
open KTheory.Bass.TwoChartStable Topology.LoopPrespectrum

universe u

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] Waldhausen.Additivity.KCommGroup

variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left] (a : Under R)

/-- The literal ambient stage-zero coefficient square. -/
abbrev coefficientConnectiveSquare : Arrow (Arrow Topology.LoopPrespectrum.{u+1}) :=
  Functor.obj (Functor.mapArrow (Functor.mapArrow
    (boundedAboveFlatCoefficientAmbientBassDiagram P 0))) (laurentUnderSquare R a)

local notation "S" => (coefficientConnectiveSquare P a)
local notation "X" => (compactFiber P a)
local notation "K" n => connectivePerfectKFunctor n
local notation "E" n => boundedAboveFlatCoefficientAmbientBassConnectiveNatIso P n

/-- The two original polynomial coordinates compare with the actual stable polynomial group. -/
def coefficientConnectivePolynomialIso (n : ℕ) :
    (K n).obj (op (Relative.polynomialFunctor.obj X)) ≅
      (stableHomotopyFunctor (n : ℤ)).obj (S).left.right :=
  (K n).mapIso (quasiCompactScheme.isoMk (compactFiberPolynomialIso P a)).op ≪≫
    (E n).app ((polynomialUnderFunctor R).obj a)

/-- The original Laurent coordinate compares with the actual stable Laurent group. -/
def coefficientConnectiveLaurentIso (n : ℕ) :
    (K n).obj (op (Relative.laurentFunctor.obj X)) ≅
      (stableHomotopyFunctor (n : ℤ)).obj (S).right.right :=
  (K n).mapIso (quasiCompactScheme.isoMk (compactFiberLaurentIso P a)).op ≪≫
    (E n).app ((laurentUnderFunctor R).obj a)

/-- Coefficient pullback agrees with the unchanged spectral source leg. -/
theorem coefficientConnectivePolynomialIso_comm (n : ℕ) :
    (K n).map ((Relative.polynomialProjection.app X).op) ≫
      (coefficientConnectivePolynomialIso P a n).hom =
    (E n).hom.app a ≫ (stableHomotopyFunctor (n : ℤ)).map (S).left.hom := by
  have h := (E n).hom.naturality ((polynomialUnderCoefficient R).app a)
  change (K n).map ((boundedAboveFlatCoefficientQuasiCompactRow P).map
      ((polynomialUnderCoefficient R).app a)) ≫
    (E n).hom.app ((polynomialUnderFunctor R).obj a) =
      (E n).hom.app a ≫
        (stableHomotopyFunctor (n : ℤ)).map (S).left.hom at h
  rw [← h]
  change (K n).map (Relative.polynomialProjection.app X).op ≫
    ((K n).map _ ≫ (E n).hom.app _) = (K n).map _ ≫ (E n).hom.app _
  rw [← Category.assoc, ← Functor.map_comp]
  congr 2
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  exact compactFiberPolynomialIso_projection P a

/-- The original positive Laurent leg commutes with both geometric and spectral comparisons. -/
theorem coefficientConnectiveLaurentIso_plus (n : ℕ) :
    (K n).map (Relative.plus.app X).op ≫ (coefficientConnectiveLaurentIso P a n).hom =
      (coefficientConnectivePolynomialIso P a n).hom ≫
        (stableHomotopyFunctor (n : ℤ)).map (S).hom.right := by
  change (K n).map _ ≫ ((K n).map _ ≫ (E n).hom.app _) =
    ((K n).map _ ≫ (E n).hom.app _) ≫ _
  have h := (E n).hom.naturality ((underToLaurent R).app a)
  change (K n).map ((boundedAboveFlatCoefficientQuasiCompactRow P).map
      ((underToLaurent R).app a)) ≫
    (E n).hom.app ((laurentUnderFunctor R).obj a) =
      (E n).hom.app ((polynomialUnderFunctor R).obj a) ≫
        (stableHomotopyFunctor (n : ℤ)).map (S).hom.right at h
  rw [Category.assoc, ← h,
    ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  exact (compactFiberLaurentIso_charts P a).1.symm

/-- The original inverse-coordinate leg commutes with both comparisons, before its minus sign. -/
theorem coefficientConnectiveLaurentIso_minus (n : ℕ) :
    (K n).map (Relative.minus.app X).op ≫ (coefficientConnectiveLaurentIso P a n).hom =
      (coefficientConnectivePolynomialIso P a n).hom ≫
        (stableHomotopyFunctor (n : ℤ)).map (S).right.hom := by
  change (K n).map _ ≫ ((K n).map _ ≫ (E n).hom.app _) =
    ((K n).map _ ≫ (E n).hom.app _) ≫ _
  have h := (E n).hom.naturality ((underToLaurentInvert R).app a)
  change (K n).map ((boundedAboveFlatCoefficientQuasiCompactRow P).map
      ((underToLaurentInvert R).app a)) ≫
    (E n).hom.app ((laurentUnderFunctor R).obj a) =
      (E n).hom.app ((polynomialUnderFunctor R).obj a) ≫
        (stableHomotopyFunctor (n : ℤ)).map (S).right.hom at h
  rw [Category.assoc, ← h,
    ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  exact (compactFiberLaurentIso_charts P a).2.symm

/-- Coordinate conversion from the original product to the actual spectral chart biproduct. -/
def coefficientConnectiveChartPairIso (n : ℕ) :
    AddCommGrpCat.of (Additive
      (((perfectComplexesWaldhausen (Relative.polynomialFunctor.obj X).obj.toRingedSpace).K n) ×
        ((perfectComplexesWaldhausen
          (Relative.polynomialFunctor.obj X).obj.toRingedSpace).K n))) ≅
      (chartComplex S (n : ℤ)).X₂ :=
  (AddEquiv.refl _).toAddCommGrpIso ≪≫
    (AddCommGrpCat.biprodIsoProd ((K n).obj (op (Relative.polynomialFunctor.obj X)))
      ((K n).obj (op (Relative.polynomialFunctor.obj X)))).symm ≪≫
    biprod.mapIso (coefficientConnectivePolynomialIso P a n)
      (coefficientConnectivePolynomialIso P a n)

/-- The spectral chart complex is isomorphic to the original perfect K-theory chart complex. -/
def coefficientConnectiveChartIso [QuasiSeparatedSpace P.left] (n : ℕ) :
    letI : QuasiSeparatedSpace (X).obj := quasiSeparatedSpace_space (op P, a)
    positiveBassChartComplex X n ≅ chartComplex S (n : ℤ) := by
  letI : QuasiSeparatedSpace (X).obj := quasiSeparatedSpace_space (op P, a)
  let PP := (K n).obj (op (Relative.polynomialFunctor.obj X))
  let e : (positiveBassChartComplex X n).X₂ ≅ AddCommGrpCat.of (PP × PP) :=
    (AddEquiv.refl (PP × PP)).toAddCommGrpIso
  let b := AddCommGrpCat.biprodIsoProd PP PP
  let ep := coefficientConnectivePolynomialIso P a n
  let el := coefficientConnectiveLaurentIso P a n
  let eo := (E n).app a
  refine ShortComplex.isoMk eo (coefficientConnectiveChartPairIso P a n) el ?_ ?_
  · change eo.hom ≫ biprod.lift _ _ =
      AddCommGrpCat.ofHom (relativePolynomialPair X n).toAdditive ≫
        (e.hom ≫ b.inv ≫ biprod.map ep.hom ep.hom)
    have hf : AddCommGrpCat.ofHom (relativePolynomialPair X n).toAdditive ≫
        e.hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.fst PP PP) =
      (K n).map (Relative.polynomialProjection.app X).op := rfl
    have hg : AddCommGrpCat.ofHom (relativePolynomialPair X n).toAdditive ≫
        e.hom ≫ AddCommGrpCat.ofHom (AddMonoidHom.snd PP PP) =
      (K n).map (Relative.polynomialProjection.app X).op := rfl
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst]
      have hp : b.inv ≫ biprod.fst = AddCommGrpCat.ofHom (AddMonoidHom.fst PP PP) :=
        AddCommGrpCat.biprodIsoProd_inv_comp_fst PP PP
      rw [← Category.assoc b.inv biprod.fst ep.hom, hp, ← Category.assoc e.hom _ ep.hom,
        ← Category.assoc _ _ ep.hom, hf]
      exact (coefficientConnectivePolynomialIso_comm P a n).symm
    · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd]
      have hp : b.inv ≫ biprod.snd = AddCommGrpCat.ofHom (AddMonoidHom.snd PP PP) :=
        AddCommGrpCat.biprodIsoProd_inv_comp_snd PP PP
      rw [← Category.assoc b.inv biprod.snd ep.hom, hp, ← Category.assoc e.hom _ ep.hom,
        ← Category.assoc _ _ ep.hom, hg]
      exact (coefficientConnectivePolynomialIso_comm P a n).symm
  · let f := (K n).map (Relative.plus.app X).op
    let g := (K n).map (Relative.minus.app X).op
    have hd : positiveBassDifferenceHom X n = e.hom ≫ b.inv ≫ biprod.desc f (-g) := by
      rw [AddCommGrpCat.biprodIsoProd_inv_comp_desc]
      rfl
    change (e.hom ≫ b.inv ≫ biprod.map ep.hom ep.hom) ≫ biprod.desc _ (-_) =
      positiveBassDifferenceHom X n ≫ el.hom
    rw [hd]
    simp only [Category.assoc]
    congr 2
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc_assoc, biprod.inl_desc]
      exact (coefficientConnectiveLaurentIso_plus P a n).symm
    · simp only [biprod.inr_map_assoc, biprod.inr_desc_assoc, biprod.inr_desc,
        Preadditive.comp_neg, Preadditive.neg_comp]
      exact congrArg Neg.neg (coefficientConnectiveLaurentIso_minus P a n).symm

/-- The literal ambient spectral chart complex is exact in every connective degree. -/
theorem coefficientConnectiveChart_exact [QuasiSeparatedSpace P.left] (n : ℕ) :
    (chartComplex S (n : ℤ)).Exact := by
  let : QuasiSeparatedSpace (X).obj := quasiSeparatedSpace_space (op P, a)
  exact ShortComplex.exact_of_iso (coefficientConnectiveChartIso P a n)
    (positiveBassChartComplex_exact X n)

/-- The actual original cokernels compare through the same literal Laurent representatives. -/
def coefficientConnectiveCokernelIso [QuasiSeparatedSpace P.left] (n : ℕ) :
    cokernel (positiveBassDifferenceHom X n) ≅ cokernel (chartDifference S (n : ℤ)) := by
  let e := coefficientConnectiveChartIso P a n
  exact cokernel.mapIso _ _ (coefficientConnectiveChartPairIso P a n)
    (coefficientConnectiveLaurentIso P a n) e.hom.comm₂₃.symm

/-- The cokernel comparison is induced by the original Laurent group isomorphism. -/
@[reassoc]
theorem coefficientConnectiveCokernelIso_π [QuasiSeparatedSpace P.left] (n : ℕ) :
    cokernel.π (positiveBassDifferenceHom X n) ≫ (coefficientConnectiveCokernelIso P a n).hom =
      (coefficientConnectiveLaurentIso P a n).hom ≫ cokernel.π (chartDifference S (n : ℤ)) :=
  cokernel.π_desc _ _ _

end AlgebraicGeometry.Scheme.Modules
