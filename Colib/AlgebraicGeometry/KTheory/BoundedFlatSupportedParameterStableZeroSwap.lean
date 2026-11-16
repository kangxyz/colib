/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatSupportedParameterDoubleForwardQuotient
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeContractionBlockSwap
public import Colib.KTheory.Bass.TwoChartMapIso
public import Colib.AlgebraicGeometry.KTheory.Bass.ModelDoubleLaurentSign
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedParameterCoefficientSeed

/-! # The actual supported degree-zero parameter quotient swap

The degree-two swap gives the degree-zero swap via both actual supported unit isomorphisms.
Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
SupportedParameterDoubleCorrection.lean`, revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open CommRingCat.PolynomialLaurent KTheory.Bass.TwoChart
universe u
namespace AlgebraicGeometry.Scheme.Modules.SupportedParameterCoefficientUnitOperation
open SupportedParameterSpecQuotientTransport KTheory.Bass.GeometricConeInterchange
local notation "R" => CommRingCat.of (ULift ℤ)
local notation "p" => NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus
local notation "m" => NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus
local notation "L" => AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.op
local notation "P₀" => AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialFunctor.op
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q) [IsOpenImmersion f.left]
  [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- The four original Spec chart isomorphisms make the twice-contracted comparison invertible. -/
theorem doubleForwardQuotient_doubleMap_spec_isIso (a : Under R) :
    IsIso ((contractionMap p m (contractionMap p m (doubleForwardQuotient f.left))).app
      (specRow.obj a)) := by
  have hPP : IsIso ((doubleForwardQuotient f.left).app ((P₀).obj ((P₀).obj (specRow.obj a)))) :=
    (NatTrans.isIso_app_iff_of_iso (doubleForwardQuotient f.left)
      (polynomialIso.app ((polynomialUnderFunctor R).obj a) ≪≫
        (P₀).mapIso (polynomialIso.app a))).mp
        (doubleForwardQuotient_spec_isIso f
          ((polynomialUnderFunctor R).obj ((polynomialUnderFunctor R).obj a)))
  have hLP : IsIso ((doubleForwardQuotient f.left).app ((L).obj ((P₀).obj (specRow.obj a)))) :=
    (NatTrans.isIso_app_iff_of_iso (doubleForwardQuotient f.left)
      (laurentIso.app ((polynomialUnderFunctor R).obj a) ≪≫
        (L).mapIso (polynomialIso.app a))).mp
        (doubleForwardQuotient_spec_isIso f
          ((laurentUnderFunctor R).obj ((polynomialUnderFunctor R).obj a)))
  have hPL : IsIso ((doubleForwardQuotient f.left).app ((P₀).obj ((L).obj (specRow.obj a)))) :=
    (NatTrans.isIso_app_iff_of_iso (doubleForwardQuotient f.left)
      (polynomialIso.app ((laurentUnderFunctor R).obj a) ≪≫
        (P₀).mapIso (laurentIso.app a))).mp
        (doubleForwardQuotient_spec_isIso f
          ((polynomialUnderFunctor R).obj ((laurentUnderFunctor R).obj a)))
  have hLL : IsIso ((doubleForwardQuotient f.left).app ((L).obj ((L).obj (specRow.obj a)))) :=
    (NatTrans.isIso_app_iff_of_iso (doubleForwardQuotient f.left)
      (doubleLaurentIso a)).mp inferInstance
  exact isIso_doubleContractionMap_app p m (doubleForwardQuotient f.left) (specRow.obj a)

private theorem natural_negative_at_iso {C : Type*} [Category C]
    {F : C ⥤ AddCommGrpCat.{u + 1}} (t : F ⟶ F) {A B : C} (e : A ≅ B)
    (h : t.app A = -𝟙 _) : t.app B = -𝟙 _ := by
  apply (cancel_epi (F.map e.hom)).1
  rw [t.naturality, h]
  simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.id_comp, Category.comp_id]

private theorem sign_cancel {A B : AddCommGrpCat.{u + 1}}
    (v : A ⟶ B) [Mono v] (s : A ⟶ A) (t : B ⟶ B)
    (hs : v ≫ t = s ≫ v) (ht : t = -𝟙 _) : s = -𝟙 _ := by
  apply (cancel_mono v).1
  rw [← hs, ht]
  simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.id_comp, Category.comp_id]

/-- The genuine supported degree-zero double quotient has the actual negative variable swap. -/
theorem doubleContractionSwap_stableZero_spec (a : Under R) :
    PolynomialLaurent.Relative.doubleContractionSwap
      (quasiCompactStableFunctor f.left 0) (specRow.obj a) = -𝟙 _ := by
  have hLL := natural_negative_at_iso
    (PolynomialLaurent.Relative.doubleContractionSwapNatIso
      (quasiCompactStableFunctor f.left 2)).hom (doubleLaurentIso a)
    (doubleContractionSwap_stableTwo_spec f
      ((laurentUnderFunctor R).obj ((laurentUnderFunctor R).obj a)))
  have ht := PolynomialLaurent.Relative.doubleContractionSwap_neg_contraction_contraction_app
    (quasiCompactStableFunctor f.left 2) (specRow.obj a) hLL
  have := doubleForwardQuotient_doubleMap_spec_isIso f a
  exact sign_cancel _ _ _
    (PolynomialLaurent.Relative.doubleContractionSwap_groupMap
      (doubleForwardQuotient f.left) (specRow.obj a)) ht

/-- The geometric swap has the same sign on the original supported parameter diagram. -/
theorem parameterDiagram_quotient_swap (a : Under R) :
    PolynomialLaurent.Relative.doubleContractionSwap
      (quasiCompactStableZero (GlobalSupportedParameterCoefficient.parameterDiagram f))
      (specRow.obj a) = -𝟙 _ :=
  doubleContractionSwap_stableZero_spec f a

end AlgebraicGeometry.Scheme.Modules.SupportedParameterCoefficientUnitOperation
