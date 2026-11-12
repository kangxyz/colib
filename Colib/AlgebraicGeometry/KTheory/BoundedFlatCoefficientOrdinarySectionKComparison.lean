/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientEvaluationKComparison
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSections
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSectionWaldhausen
/-! # Original ordinary coefficient evaluation on K-groups

The public general evaluation equivalence is reused. Two private original computation
lemmas support only the ordinary section specialization and its actual object-class equation.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Waldhausen
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
section OriginalObjectClass
variable {C : Type (u + 1)} [Category.{u + 1} C]
  {D : Type (u + 1)} [Category.{u} D]
  (V : Structure C) (W : Structure D) (e : C ≌ D)
  (hE : IsExact V.cof V.weq W.cof W.weq e.functor)
  (hEi : IsExact W.cof W.weq V.cof V.weq e.inverse)
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSectionKComparison.lean:45"
  "adaptation" "Original ordinary section evaluation K-equivalence and object class"]
private theorem evaluationKEquiv_apply (n : ℕ) (x : V.K n) :
    boundedAboveFlatCoefficientEvaluationKEquiv V W e hE hEi n x =
      (W.asSmallKEquiv n).symm (KMap (hE.comp W.asSmall_up_exact) n x) := rfl

@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSectionKComparison.lean:49"
  "adaptation" "Original ordinary section evaluation K-equivalence and object class"]
private theorem evaluationKEquiv_objectClass (A : C) :
    boundedAboveFlatCoefficientEvaluationKEquiv V W e hE hEi 0 (V.kZeroObjectClass A) =
      W.kZeroObjectClass (e.functor.obj A) := by
  rw [evaluationKEquiv_apply]
  apply (W.asSmallKEquiv 0).injective
  rw [MulEquiv.apply_symm_apply, Structure.asSmallKEquiv_objectClass]
  exact KMap_kZeroObjectClass (hE.comp W.asSmall_up_exact) A

end OriginalObjectClass
variable {R : CommRingCat.{u}}

/-- Original identity evaluation computes all native bounded-flat fiber K-groups. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSectionKComparison.lean:91"
  "adaptation" "Original ordinary section evaluation K-equivalence and object class"]
def boundedAboveFlatCoefficientSectionKEquiv (i : Index R) (n : ℕ) :
    (boundedAboveFlatCoefficientSectionWaldhausen i).K n ≃*
      (RingedSpace.boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).K n :=
  boundedAboveFlatCoefficientEvaluationKEquiv (boundedAboveFlatCoefficientSectionWaldhausen i)
    (RingedSpace.boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace)
      (boundedAboveFlatCoefficientSectionEquivalence i)
    (boundedAboveFlatCoefficientOriginalEvaluation_exact i)
    (boundedAboveFlatCoefficientSectionEquivalence_inverse_exact i) n

/-- Original evaluation retains exactly the original bounded-flat object's K-zero class. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSectionKComparison.lean:100"
  "adaptation" "Original ordinary section evaluation object class", simp]
theorem boundedAboveFlatCoefficientSectionKEquiv_objectClass (i : Index R)
    (S : BoundedAboveFlatCoefficientSections i) :
    boundedAboveFlatCoefficientSectionKEquiv i 0
        ((boundedAboveFlatCoefficientSectionWaldhausen i).kZeroObjectClass S) =
      (RingedSpace.boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).kZeroObjectClass
        ((boundedAboveFlatCoefficientOriginalEvaluation i).obj S) :=
  evaluationKEquiv_objectClass
    (boundedAboveFlatCoefficientSectionWaldhausen i)
      (RingedSpace.boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace)
    (boundedAboveFlatCoefficientSectionEquivalence i)
      (boundedAboveFlatCoefficientOriginalEvaluation_exact i)
    (boundedAboveFlatCoefficientSectionEquivalence_inverse_exact i) S

end AlgebraicGeometry.Scheme.Modules
