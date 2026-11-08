/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.WeakArrow.Structure
public import Colib.KTheory.Waldhausen.Functoriality

/-!
# The original first-leg K-equivalence in weak-arrow factorization

The literal identity-arrow diagonal is inverse on every original connective
K-group to the source projection, by its actual weak counit. Original chosen-zero
rebasing and both factorization triangles are retained. Thus the unchanged
original functor KMap is bijective precisely when the actual target projection
KMap is bijective. This does not assume or prove the second-leg approximation.
The object universe may dominate the hom universe, covering geometric categories.

Implementation provenance: `Quillen/Waldhausen/WeakArrow/KEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original categories, maps, hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.WeakArrow
variable {C D : Type (max u v)} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) (F : C ⥤ D)
  (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- The original source-projection K-map is a left inverse to the actual diagonal K-map. -/
theorem KMap_source_diagonal (n : ℕ) (x : V.K n) :
    KMap (source_exact V W F hF) n (KMap (diagonal_exact V W F hF) n x) = x := by
  have h := (KMap_comp_KMap (diagonal_exact V W F hF) (source_exact V W F hF) n).symm
  have he : KMap ((diagonal_exact V W F hF).comp (source_exact V W F hF)) n =
      KMap (IsExact.id V.cof V.weq) n := rfl
  rw [he, KMap_id] at h
  exact (DFunLike.congr_fun h x).symm

/-- The stored original weak arrow gives the other inverse equality, with original zero rebasing. -/
theorem KMap_diagonal_source (n : ℕ) (x : (waldhausenStructure V W F hF).K n) :
    KMap (diagonal_exact V W F hF) n (KMap (source_exact V W F hF) n x) = x := by
  have h := KMap_eq_of_weakNatTrans
    ((source_exact V W F hF).comp (diagonal_exact V W F hF))
    (IsExact.id (waldhausenStructure V W F hF).cof (waldhausenStructure V W F hF).weq)
    (counit W F) (counit_weak V W F hF) n
  exact (DFunLike.congr_fun (KMap_comp_KMap (source_exact V W F hF)
      (diagonal_exact V W F hF) n).symm x).symm.trans
    (by simpa only [KMap_id, MonoidHom.id_apply] using DFunLike.congr_fun h x)

/-- The genuine weak-arrow enlargement is equivalent on original K-groups in every degree. -/
@[colib_tag "COL-0309",
  colib_ref "quillen" "Quillen/Waldhausen/WeakArrow/KEquivalence.lean:55" "adaptation"
    "Actual diagonal and source KMaps are inverse in every connective degree"]
def diagonalKEquiv (n : ℕ) : V.K n ≃* (waldhausenStructure V W F hF).K n where
  toFun := KMap (diagonal_exact V W F hF) n
  invFun := KMap (source_exact V W F hF) n
  left_inv := KMap_source_diagonal V W F hF n
  right_inv := KMap_diagonal_source V W F hF n
  map_mul' := (KMap (diagonal_exact V W F hF) n).map_mul

@[simp] theorem diagonalKEquiv_apply (n : ℕ) (x : V.K n) :
    diagonalKEquiv V W F hF n x = KMap (diagonal_exact V W F hF) n x := rfl

/-- The second leg and first-leg equivalence compose to the unchanged original functor K-map. -/
@[colib_tag "COL-0309",
  colib_ref "quillen" "Quillen/Waldhausen/WeakArrow/KEquivalence.lean:66" "adaptation"
    "Factorization of the actual canonical KMap through the identity-arrow diagonal"]
theorem KMap_factor (n : ℕ) :
    (KMap (target_exact V W F hF) n).comp (diagonalKEquiv V W F hF n).toMonoidHom = KMap hF n := by
  exact (KMap_comp_KMap (diagonal_exact V W F hF) (target_exact V W F hF) n).symm.symm

/-- Projection comparison commutes on the original homomorphisms, not merely abstract groups. -/
theorem KMap_target_eq (n : ℕ) :
    KMap (target_exact V W F hF) n = (KMap hF n).comp (KMap (source_exact V W F hF) n) := by
  have h := KMap_eq_of_weakNatTrans ((source_exact V W F hF).comp hF)
    (target_exact V W F hF) (comparison W F) (comparison_weak W F) n
  exact h.symm.trans (KMap_comp_KMap (source_exact V W F hF) hF n).symm

/-- Proving the actual target projection bijective suffices for the unchanged original K-map. -/
theorem KMap_bijective_iff_target (n : ℕ) : Function.Bijective (KMap hF n) ↔
    Function.Bijective (KMap (target_exact V W F hF) n) := by
  rw [← KMap_factor V W F hF n]
  exact (diagonalKEquiv V W F hF n).bijective.of_comp_iff (KMap (target_exact V W F hF) n)
end CategoryTheory.Waldhausen.WeakArrow
