/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.WeakArrow.RelativeStructure
public import Colib.KTheory.Waldhausen.Functoriality

/-! # Original first-leg K-equivalence with relative weak classes

Implementation provenance: `Quillen/Waldhausen/WeakArrow/RelativeKEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original categories, maps, hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.WeakArrow.Relative
variable {C D E : Type (max u v)} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  (V : Structure C) (W : Structure D) (U : Structure E)
  (F : C ⥤ D) (G : D ⥤ E)
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact W.cof W.weq U.cof U.weq G)
  [U.weq.HasTwoOutOfThreeProperty]

/-- The original source-projection K-map is a left inverse to the actual diagonal K-map. -/
theorem KMap_source_diagonal (n : ℕ) (x : (sourceStructure V W U F G hF hG).K n) :
    KMap (source_exact V W U F G hF hG) n (KMap (diagonal_exact V W U F G hF hG) n x) = x := by
  have h := (KMap_comp_KMap (diagonal_exact V W U F G hF hG) (source_exact V W U F G hF hG) n).symm
  have he : KMap ((diagonal_exact V W U F G hF hG).comp (source_exact V W U F G hF hG)) n =
      KMap (IsExact.id (sourceStructure V W U F G hF hG).cof (sourceStructure V W U F G hF
        hG).weq) n := rfl
  rw [he, KMap_id] at h
  exact (DFunLike.congr_fun h x).symm

/-- The stored original weak arrow gives the other inverse equality, with original zero rebasing. -/
theorem KMap_diagonal_source (n : ℕ) (x : (arrowStructure V W U F G hF hG).K n) :
    KMap (diagonal_exact V W U F G hF hG) n (KMap (source_exact V W U F G hF hG) n x) = x := by
  have h := KMap_eq_of_weakNatTrans
    ((source_exact V W U F G hF hG).comp (diagonal_exact V W U F G hF hG))
    (IsExact.id (arrowStructure V W U F G hF hG).cof (arrowStructure V W U F G hF hG).weq)
    (counit W F) (counit_weak V W U F G hF hG) n
  exact (DFunLike.congr_fun (KMap_comp_KMap (source_exact V W U F G hF hG)
      (diagonal_exact V W U F G hF hG) n).symm x).symm.trans
    (by simpa only [KMap_id, MonoidHom.id_apply] using DFunLike.congr_fun h x)

/-- The genuine weak-arrow enlargement is equivalent on original K-groups in every degree. -/
@[colib_tag "COL-0309",
  colib_ref "quillen" "Quillen/Waldhausen/WeakArrow/RelativeKEquivalence.lean:48" "adaptation"
    "Actual diagonal K-equivalence with relative inverse-image weak classes"]
def diagonalKEquiv (n : ℕ) : (sourceStructure V W U F G hF hG).K n ≃* (arrowStructure V W U F G
    hF hG).K n where
  toFun := KMap (diagonal_exact V W U F G hF hG) n
  invFun := KMap (source_exact V W U F G hF hG) n
  left_inv := KMap_source_diagonal V W U F G hF hG n
  right_inv := KMap_diagonal_source V W U F G hF hG n
  map_mul' := (KMap (diagonal_exact V W U F G hF hG) n).map_mul

@[simp] theorem diagonalKEquiv_apply (n : ℕ) (x : (sourceStructure V W U F G hF hG).K n) :
    diagonalKEquiv V W U F G hF hG n x = KMap (diagonal_exact V W U F G hF hG) n x := rfl

/-- The second leg and first-leg equivalence compose to the unchanged original functor K-map. -/
theorem KMap_factor (n : ℕ) :
    (KMap (target_exact V W U F G hF hG) n).comp (diagonalKEquiv V W U F G hF hG n).toMonoidHom
      = KMap (functor_exact V W U F G hF hG) n := by
  exact (KMap_comp_KMap (diagonal_exact V W U F G hF hG) (target_exact V W U F G hF hG) n).symm.symm

/-- Bijectivity of the unchanged original relative functor is equivalent to
bijectivity of the actual target on fine weak-arrow objects. -/
@[colib_tag "COL-0309",
  colib_ref "quillen" "Quillen/Waldhausen/WeakArrow/RelativeKEquivalence.lean:68" "adaptation"
    "Original relative KMap bijectivity is equivalent to target KMap bijectivity"]
theorem KMap_bijective_iff_target (n : ℕ) :
    Function.Bijective (KMap (functor_exact V W U F G hF hG) n) ↔
    Function.Bijective (KMap (target_exact V W U F G hF hG) n) := by
  rw [← KMap_factor V W U F G hF hG n]
  exact (diagonalKEquiv V W U F G hF hG n).bijective.of_comp_iff
    (KMap (target_exact V W U F G hF hG) n)
end CategoryTheory.Waldhausen.WeakArrow.Relative
