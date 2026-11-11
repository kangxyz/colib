/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalOpenPairDiagram

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterCoefficientModels
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalFullOpenModels

/-! # The actual full-open restriction square of integral parameter Models -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The original full restriction, retaining its actual change-of-weakness factorization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterCoefficientRestriction.lean:28"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
def parameterFullRestriction : ParameterModels.ambient Q.left ⟶ ParameterModels.ambient P.left :=
  ParameterModels.changeWeak f.left ≫ ParameterModels.openRestriction f.left

/-- Actual row symmetry commutes with the complete original full-open restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterCoefficientRestriction.lean:32"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem fullRestriction_model_square :
    Functor.whiskerLeft specUnder (parameterFullRestriction f) ≫ (parameterRowModelIso P).hom =
      (parameterRowModelIso Q).hom ≫ globalOpenFineRestriction f := by
  apply NatTrans.ext
  funext a
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, parameterRowModelIso_hom_app]
  change boundedAboveFlatGlobalSectionModelFunctor.map
      ((baseProductTransformation (specULiftZIsTerminal.from P.left) (specULiftZIsTerminal.from
        Q.left)
        f.left (specULiftZIsTerminal.hom_ext _ _)).app (Spec a.right)).op ≫
      boundedAboveFlatGlobalSectionModelFunctor.map (canonicalRowIso P a).hom.op =
    boundedAboveFlatGlobalSectionModelFunctor.map (canonicalRowIso Q a).hom.op ≫
      boundedAboveFlatGlobalSectionModelFunctor.map (schemeMap f a).op
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    ← op_comp, ← op_comp, ← canonicalRowIso_scheme]

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient

