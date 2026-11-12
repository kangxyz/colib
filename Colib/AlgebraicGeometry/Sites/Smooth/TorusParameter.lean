/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Torus

/-!
# The parameter coordinate of a torus power

Swapping the right parameter to the first coordinate respects every actual
identity insertion. The parameter identity itself factors through the
zeroth identity axis of the enlarged torus power.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (S : Scheme.{u})

/-- Place the right-hand multiplicative parameter in coordinate zero. -/
def torusPowerParameterSwap (q : ℕ) :
    product (torusPower S q) (multiplicativeGroupObject S) ⟶ torusPower S (q + 1) :=
  productLift (productSnd (torusPower S q) (multiplicativeGroupObject S))
    (productFst (torusPower S q) (multiplicativeGroupObject S))

@[reassoc]
theorem torusPowerParameterSwap_coordinate_zero (q : ℕ) :
    torusPowerParameterSwap S q ≫ torusCoordinate S (q + 1) 0 =
      productSnd (torusPower S q) (multiplicativeGroupObject S) :=
  productLift_fst _ _

@[reassoc]
theorem torusPowerParameterSwap_coordinate_succ (q : ℕ) (j : Fin q) :
    torusPowerParameterSwap S q ≫ torusCoordinate S (q + 1) j.succ =
      productFst (torusPower S q) (multiplicativeGroupObject S) ≫ torusCoordinate S q j := by
  let swap : product (torusPower S q) (multiplicativeGroupObject S) ⟶
      product (multiplicativeGroupObject S) (torusPower S q) := torusPowerParameterSwap S q
  have hSnd : swap ≫ productSnd (multiplicativeGroupObject S) (torusPower S q) =
      productFst (torusPower S q) (multiplicativeGroupObject S) :=
    productLift_snd _ _
  change swap ≫ (productSnd (multiplicativeGroupObject S) (torusPower S q) ≫
    torusCoordinate S q j) = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun g ↦ g ≫ torusCoordinate S q j) hSnd)

/-- Each identity axis is shifted by one when the parameter is placed first. -/
theorem torusInsertOne_parameterSwap (q : ℕ) (i : Fin (q + 1)) :
    productMap (torusInsertOne S q i) (𝟙 (multiplicativeGroupObject S)) ≫
        torusPowerParameterSwap S (q + 1) =
      torusPowerParameterSwap S q ≫ torusInsertOne S (q + 1) i.succ := by
  apply torusPower_hom_ext S (q + 2)
  intro j
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove i.succ j
  · simp only [Category.assoc, torusPowerParameterSwap_coordinate_succ,
      productMap_fst_assoc, torusInsertOne_coordinate_self]
    have hb : productFst (torusPower S q) (multiplicativeGroupObject S) ≫
        torusPowerToBase S q =
        torusPowerParameterSwap S q ≫ torusPowerToBase S (q + 1) :=
      torusPower_hom_ext S 0 (fun t ↦ Fin.elim0 t)
    simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ torusOne S) hb
  · simp only [Category.assoc, torusInsertOne_coordinate_succAbove]
    refine Fin.cases ?_ (fun l ↦ ?_) j
    · simp only [Fin.succ_succAbove_zero, torusPowerParameterSwap_coordinate_zero,
        productMap_snd, Category.comp_id]
    · simp only [Fin.succ_succAbove_succ, torusPowerParameterSwap_coordinate_succ,
        productMap_fst_assoc, torusInsertOne_coordinate_succAbove]

/-- At parameter one, the map factors through the actual identity axis in coordinate zero. -/
theorem torusOne_parameterSwap (q : ℕ) :
    productMap (𝟙 (torusPower S q)) (torusOne S) ≫ torusPowerParameterSwap S q =
      productFst (torusPower S q) (base S) ≫ torusInsertOne S q 0 := by
  apply torusPower_hom_ext S (q + 1)
  intro j
  refine Fin.cases ?_ (fun l ↦ ?_) j
  · simp only [Category.assoc, torusPowerParameterSwap_coordinate_zero,
      productMap_snd, torusInsertOne_coordinate_self]
    have hb : productSnd (torusPower S q) (base S) =
        productFst (torusPower S q) (base S) ≫ torusPowerToBase S q :=
      torusPower_hom_ext S 0 (fun t ↦ Fin.elim0 t)
    simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ torusOne S) hb
  · have hInsert : torusInsertOne S q 0 ≫ torusCoordinate S (q + 1) l.succ =
        torusCoordinate S q l := by
      simpa only [Fin.zero_succAbove] using torusInsertOne_coordinate_succAbove S q 0 l
    simp only [Category.assoc, torusPowerParameterSwap_coordinate_succ, productMap_fst_assoc,
      Category.id_comp, hInsert]

end AlgebraicGeometry.Scheme.SmoothSite
