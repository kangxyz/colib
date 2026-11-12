/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.ExactEquivalence
public import Colib.KTheory.Waldhausen.GrothendieckComparison.AsSmall


/-!
# The canonical original native section evaluation on K-groups

One common-universe evaluation bridge retains the original exact forward map and
universe lowering. Its canonical fine-fiber specialization is shared by native open
cofinality and actual geometric spectrum evaluation. The original evaluated object
classes and natural-isomorphism K-map transport are unchanged, including degree zero.
-/
@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
universe u
namespace AlgebraicGeometry.Scheme.Modules

section CoefficientOpenKTransport
variable {C C' : Type (u + 1)} [Category.{u + 1} C] [Category.{u + 1} C']
  {D D' : Type (u + 1)} [Category.{u} D] [Category.{u} D']
  (V : Structure C) (W : Structure D) (e : C ≌ D)
  (hE : IsExact V.cof V.weq W.cof W.weq e.functor)
  (hEi : IsExact W.cof W.weq V.cof V.weq e.inverse)

/-- The original exact evaluation, with only the existing universe lift and lowering. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSectionKComparison.lean:40"
  "adaptation" "Original evaluation K-comparison and actual supported restriction cofinality"]
def boundedAboveFlatCoefficientEvaluationKEquiv (n : ℕ) : V.K n ≃* W.K n :=
  (KEquivOfExactEquivalence (e.trans AsSmall.equiv)
    (hE.comp W.asSmall_up_exact) (W.asSmall_down_exact.comp hEi) n).trans
      (W.asSmallKEquiv n).symm

private theorem evaluationKEquiv_apply (n : ℕ) (x : V.K n) :
    boundedAboveFlatCoefficientEvaluationKEquiv V W e hE hEi n x =
      (W.asSmallKEquiv n).symm (KMap (hE.comp W.asSmall_up_exact) n x) := rfl

variable (V' : Structure C') (W' : Structure D') (e' : C' ≌ D')
  (hE' : IsExact V'.cof V'.weq W'.cof W'.weq e'.functor)
  (hEi' : IsExact W'.cof W'.weq V'.cof V'.weq e'.inverse)
  {F : C ⥤ C'} {G : D ⥤ D'}
  (hF : IsExact V.cof V.weq V'.cof V'.weq F)
  (hG : IsExact W.cof W.weq W'.cof W'.weq G)
  (s : F ⋙ e'.functor ≅ e.functor ⋙ G)

include s in
/-- A genuine evaluation square preserves the original KMaps across the hom universes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientSectionKComparison.lean:67"
  "adaptation" "Original evaluation K-comparison and actual supported restriction cofinality"]
theorem boundedAboveFlatCoefficientEvaluationKEquiv_natural (n : ℕ) (x : V.K n) :
    boundedAboveFlatCoefficientEvaluationKEquiv V' W' e' hE' hEi' n (KMap hF n x) =
      KMap hG n (boundedAboveFlatCoefficientEvaluationKEquiv V W e hE hEi n x) := by
  have hs :
      (KMap (hE'.comp W'.asSmall_up_exact) n).comp (KMap hF n) =
        (KMap hG.asSmall n).comp (KMap (hE.comp W.asSmall_up_exact) n) := by
    rw [KMap_comp_KMap, KMap_comp_KMap]
    exact KMap_eq_of_iso _ _ (Functor.isoWhiskerRight s AsSmall.up) n
  apply (W'.asSmallKEquiv n).injective
  have hn := DFunLike.congr_fun (asSmallKEquiv_naturality hG n)
    (boundedAboveFlatCoefficientEvaluationKEquiv V W e hE hEi n x)
  change W'.asSmallKEquiv n
      (KMap hG n (boundedAboveFlatCoefficientEvaluationKEquiv V W e hE hEi n x)) =
    KMap hG.asSmall n
      (W.asSmallKEquiv n (boundedAboveFlatCoefficientEvaluationKEquiv V W e hE hEi n x)) at hn
  simp only [evaluationKEquiv_apply, MulEquiv.apply_symm_apply] at hn ⊢
  rw [hn]
  exact DFunLike.congr_fun hs x

end CoefficientOpenKTransport

end AlgebraicGeometry.Scheme.Modules
