/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.NativeSingleUnitQuotient
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeDoubleContractionProductTransport
public import Colib.AlgebraicGeometry.KTheory.Bass.ModelDoubleLaurentSign
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationEquivalence
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationNaturality
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterCoefficientSquare

/-! # The original ambient Model inherits the actual Laurent quotient swap sign -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen.IteratedS Opposite
open CategoryTheory.Waldhausen
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.RingedSpace KTheory.Bass.TwoChart Topology.LoopPrespectrum

universe u w

namespace AlgebraicGeometry.Scheme.Modules

open GlobalSectionChangeIndex KTheory.Bass.GeometricConeInterchange PolynomialLaurent.Relative
attribute [local instance] Waldhausen.Additivity.KCommGroup

local notation "p" => NatTrans.op plus
local notation "m" => NatTrans.op minus
local notation "F" => boundedAboveFlatGlobalSectionModelFunctor
local notation "K" => CoefficientDoubleNativeUnit.boundedAboveFlatPerfectKAddFunctor 0

/-- The unchanged original stable group comparison in degree zero. -/
def rawModelZeroIso (X : Scheme.{u}ᵒᵖ) :
    (K).obj X ≅ (stableHomotopyFunctor 0).obj
      (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace)) :=
  (originalKStableEquiv (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace) 0).toAddCommGrpIso

/-- The original raw bounded-flat K₀ is the stable degree-zero group of the global Model. -/
def globalModelZeroIso (X : Scheme.{u}ᵒᵖ) :
    (K).obj X ≅ ((F ⋙ prespectrumFunctor) ⋙ stableHomotopyFunctor 0).obj X := by
  let := evaluationModel_isStableEquivalence X 0
  exact rawModelZeroIso X ≪≫
    (asIso ((stableHomotopyFunctor 0).map (prespectrumMap (evaluationModel X)))).symm

/-- The actual global normalized evaluation respects the original raw pullback maps. -/
def globalModelZeroNatIso :
    K ≅ (F ⋙ prespectrumFunctor) ⋙ stableHomotopyFunctor 0 :=
  NatIso.ofComponents globalModelZeroIso (fun {X Y} g => by
    let f := g.unop
    let H := stableHomotopyFunctor (0 : ℤ)
    let eX : H.obj (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj X)) ⟶
        H.obj (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace)) :=
      H.map (prespectrumMap (evaluationModel X))
    let eY : H.obj (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj Y)) ⟶
        H.obj (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.unop.toRingedSpace)) :=
      H.map (prespectrumMap (evaluationModel Y))
    let hX : IsIso eX := evaluationModel_isStableEquivalence X 0
    let hY : IsIso eY := evaluationModel_isStableEquivalence Y 0
    let sX := rawModelZeroIso X
    let sY := rawModelZeroIso Y
    let M := H.map (prespectrumMap (boundedAboveFlatGlobalSectionModelFunctor.map g))
    let R : H.obj (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace)) ⟶
        H.obj (originalPrespectrum (boundedAboveFlatPerfectWaldhausen Y.unop.toRingedSpace)) :=
      H.map (prespectrumMap (evaluationRawMap f))
    have he : M ≫ eY = eX ≫ R := by
      have hh := (evaluationComparison f).stableHomotopyMap_eq (0 : ℤ)
      rw [Functor.map_comp, Functor.map_comp] at hh
      exact hh
    have hn : (K).map g ≫ sY.hom = sX.hom ≫ R := by
      apply AddCommGrpCat.ext
      intro x
      exact originalKStableEquiv_exact_naturality
        (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace)
        (boundedAboveFlatPerfectWaldhausen Y.unop.toRingedSpace)
        (boundedAboveFlatPerfectPullback_isExact f) 0 x.toMul
    let : IsIso eX := hX
    let : IsIso eY := hY
    apply (cancel_mono eY).mp
    change ((K).map g ≫ (sY.hom ≫ inv (I := hY) eY)) ≫ eY =
      ((sX.hom ≫ inv (I := hX) eX) ≫ M) ≫ eY
    simp only [Category.assoc]
    have invX : inv (I := hX) eX ≫ eX ≫ R = R :=
      @IsIso.inv_hom_id_assoc _ _ _ _ eX hX _ R
    have invY : inv (I := hY) eY ≫ eY = 𝟙 _ :=
      @IsIso.inv_hom_id _ _ _ _ eY hY
    calc
      _ = (K).map g ≫ sY.hom :=
        congrArg ((K).map g ≫ ·) ((congrArg (sY.hom ≫ ·) invY).trans (Category.comp_id _))
      _ = sX.hom ≫ R := hn
      _ = _ := (congrArg (sX.hom ≫ ·)
        ((congrArg (inv (I := hX) eX ≫ ·) he).trans invX)).symm)

/-- Actual double quotient swap sign is transported through the given original natural iso. -/
theorem doubleContractionSwap_neg_of_natIso
    {G H : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}} (e : G ≅ H)
    (X : QuasiCompactSchemes.{u}ᵒᵖ) (h : doubleContractionSwap G X = -𝟙 _) :
    doubleContractionSwap H X = -𝟙 _ := by
  let e₂ := (contractionFunctor p m).mapIso ((contractionFunctor p m).mapIso e)
  have hn : e₂.hom.app X ≫ doubleContractionSwap H X =
      doubleContractionSwap G X ≫ e₂.hom.app X := doubleContractionSwap_groupMap e.hom X
  apply (cancel_epi (e₂.hom.app X)).1
  rw [hn, h]
  let a : (contraction p m (contraction p m G)).obj X ⟶
      (contraction p m (contraction p m H)).obj X := e₂.hom.app X
  change (-𝟙 _) ≫ a = a ≫ (-𝟙 _)
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.id_comp, Category.comp_id]

/-- The original global Model inherits the genuine double quotient sign through evaluation. -/
theorem globalModel_doubleContractionSwap_neg (X : QuasiCompactSchemes.{u}ᵒᵖ)
    [QuasiSeparatedSpace X.unop.obj] :
    doubleContractionSwap (quasiCompactStableZero (F ⋙ prespectrumFunctor)) X = -𝟙 _ := by
  let e : CoefficientDoubleNativeUnit.quasiCompactKFunctor 0 ≅
      quasiCompactStableZero (F ⋙ prespectrumFunctor) :=
    Functor.isoWhiskerLeft quasiCompactSchemesInclusion.op globalModelZeroNatIso
  exact doubleContractionSwap_neg_of_natIso e X
    (CoefficientDoubleNativeUnit.doubleContractionSwap_KZero_eq_neg_id X.unop)

namespace GlobalParameterCoefficient

open GlobalSupportedSection

variable (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
  [CompactSpace P.left] [QuasiSeparatedSpace P.left]

/-- The actual fixed factor is moved past both Laurent variables by the original braid. -/
theorem parameter_doubleContractionSwap_neg (X : QuasiCompactSchemes.{u}ᵒᵖ)
    [QuasiSeparatedSpace X.unop.obj] :
    doubleContractionSwap (quasiCompactStableZero (parameterDiagram P)) X = -𝟙 _ := by
  let q := specULiftZIsTerminal.from P.left
  let f := pullback.fst (specULiftZIsTerminal.from X.unop.obj) q
  let : QuasiSeparated q := QuasiSeparated.of_quasiSeparatedSpace q
  let hf : QuasiSeparated f := inferInstanceAs
    (QuasiSeparated (pullback.fst (specULiftZIsTerminal.from X.unop.obj) q))
  let : QuasiSeparatedSpace ((qcBaseProductFunctor q).op.obj X).unop.obj :=
    @quasiSeparatedSpace_of_quasiSeparated _ X.unop.obj f inferInstance hf
  exact doubleContractionSwap_neg_product_app q
    (quasiCompactStableZero (F ⋙ prespectrumFunctor)) X
    (globalModel_doubleContractionSwap_neg ((qcBaseProductFunctor q).op.obj X))

end GlobalParameterCoefficient

end AlgebraicGeometry.Scheme.Modules
