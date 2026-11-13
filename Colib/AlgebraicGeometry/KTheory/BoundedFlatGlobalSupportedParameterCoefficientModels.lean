/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Scheme.GlobalSupportedCoefficientGeometry
public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedPairDiagram
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterCoefficientModels
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedRow

/-!
# The integral supported Spec row in the original global Models

The actual open-pair row isomorphism acts through the existing supported Model functor.
Its target is the original global supported coefficient row, with the same evaluated
support predicate, exact structure, and selected zero. Forgetting support gives exactly
the ambient row isomorphism before coefficient restriction.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
open AlgebraicGeometry.Scheme.GlobalSupportedParameter GlobalSupportedSection
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- Reindexing along the original coefficient pair is the original supported row map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientModels.lean:35"
  "adaptation" "Actual supported Spec row and whole original forgetful square"]
theorem coefficientPair_supported_map {a b : Under (CommRingCat.of (ULift.{u} ℤ))}
    (g : a ⟶ b) :
    pairSupported.map ((coefficientPairs f).map g) = (supportedRow f).map g := by
  apply WideSubcategory.hom_ext
  apply CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext
  rfl

/-- The open-pair functor specializes to the unchanged original supported coefficient row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientModels.lean:42"
  "adaptation" "Actual supported Spec row and whole original forgetful square"]
def coefficientSupportedRowIso : coefficientPairs f ⋙ pairSupported ≅ supportedRow f :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro a b g
    simp only [Iso.refl_hom]
    exact coefficientPair_supported_map f g)

/-- The actual integral row symmetry on supported original global Models. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientModels.lean:49"
  "adaptation" "Actual supported Spec row and whole original forgetful square"]
def parameterSupportedRowIso :
    specUnder ⋙ ParameterModels.supported f.left ≅ supportedRow f :=
  (Functor.associator specUnder (pairs f.left).op pairSupported).symm ≪≫
    Functor.isoWhiskerRight (coefficientPairsIso f) pairSupported ≪≫
      coefficientSupportedRowIso f

/-- Every component is the original supported reindexing along the complete open-pair iso. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientModels.lean:56"
  "adaptation" "Actual supported Spec row and whole original forgetful square"]
theorem parameterSupportedRowIso_hom_app (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (parameterSupportedRowIso f).hom.app a =
      pairSupported.map (coefficientPairIso f a).hom.op := by
  change 𝟙 _ ≫ pairSupported.map (coefficientPairIso f a).hom.op ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

/-- Forgetting support gives exactly the ambient row comparison as a whole transformation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientModels.lean:63"
  "adaptation" "Actual supported Spec row and whole original forgetful square"]
theorem parameterSupportedRowIso_forget :
    (parameterSupportedRowIso f).hom ≫ supportedRowForget f =
      Functor.whiskerLeft specUnder (ParameterModels.forget f.left) ≫
        (parameterRowModelIso Q).hom := by
  apply NatTrans.ext
  funext a
  rw [NatTrans.comp_app, NatTrans.comp_app, parameterSupportedRowIso_hom_app,
    parameterRowModelIso_hom_app]
  exact pairForget.naturality (coefficientPairIso f a).hom.op

/-- Actual restriction retains the same strict supported-to-ambient coefficient square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSupportedParameterCoefficientModels.lean:74"
  "adaptation" "Actual supported Spec row and whole original forgetful square"]
theorem parameterSupportedRowIso_restriction_forget :
    (parameterSupportedRowIso f).hom ≫ supportedRowRestriction f ≫
        boundedAboveFlatCoefficientSupportedForgetModelTransformation f =
      Functor.whiskerLeft specUnder (ParameterModels.forget f.left) ≫
        parameterCoefficientRestriction Q := by
  rw [supportedRowRestriction_forget, ← Category.assoc, parameterSupportedRowIso_forget]
  rfl

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

