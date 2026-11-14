/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterCurrentNegativeCorrection
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeConjugationAllSign

/-! # Actual finite identity corrections preserve original negative classes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open KTheory.Bass KTheory.Bass.SchemeNaturalSeed
open KTheory.Bass.GeometricConeInterchange
universe u
namespace AlgebraicGeometry.Scheme.Modules
open GlobalSectionChangeIndex GlobalSupportedSection

/-- The same original integral coefficient spectrum as an actual quasi-compact parameter. -/
def coefficientParameterScheme (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    QuasiCompactSchemes.{u}ᵒᵖ :=
  op ⟨Spec a.right, inferInstanceAs (CompactSpace (Spec a.right))⟩

private theorem iso_conj_id {A B : AddCommGrpCat.{u + 1}}
    (e : A ≅ B) (q : B ≅ B) (h : q.hom = 𝟙 B) :
    (e ≪≫ q ≪≫ e.symm).hom = 𝟙 A := by
  change e.hom ≫ q.hom ≫ e.inv = 𝟙 A
  rw [h, Category.id_comp, e.hom_inv_id]

namespace GlobalParameterCoefficient
variable (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
  [CompactSpace P.left]

/-- An identity finite correction stays identity under the unchanged original class comparison. -/
theorem negativeClassCorrection_hom_of_finite_id (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (h : (finiteStageStableIso (ParameterModels.ambient P.left) i
      (specUnder.obj a) (-(i : ℤ))).hom = 𝟙 _) :
    (negativeClassCorrection P i a).hom = 𝟙 _ :=
  iso_conj_id ((finiteNegativeKComparison P i).app a)
    (finiteStageStableIso (ParameterModels.ambient P.left) i (specUnder.obj a) (-(i : ℤ))) h

end GlobalParameterCoefficient

namespace GlobalSupportedParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- An identity supported finite correction preserves the unchanged original supported classes. -/
theorem negativeClassCorrection_hom_of_finite_id (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (h : (finiteStageStableIso (ParameterModels.supported f.left) i
      (specUnder.obj a) (-(i : ℤ))).hom = 𝟙 _) :
    (negativeClassCorrection f i a).hom = 𝟙 _ :=
  iso_conj_id ((finiteNegativeKComparison f i).app a)
    (finiteStageStableIso (ParameterModels.supported f.left) i (specUnder.obj a) (-(i : ℤ))) h

end GlobalSupportedParameterCoefficient
end AlgebraicGeometry.Scheme.Modules
