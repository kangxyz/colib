/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Duality.SConstruction
public import Colib.CategoryTheory.Waldhausen.Approximation.Dual
public import Colib.KTheory.Waldhausen.Approximation.GeneralKEquivalence

/-! # Dual approximation for the original S-construction map

Actual right-to-left factorization supplies App2 in the opposite category.
The original S-map is recovered by the proved natural coordinate reversal,
and its original canonical K-map is bijective. All cylinder and dual exactness
inputs remain structural and explicit; no K-equivalence is a hypothesis.

Implementation provenance: `Quillen/Waldhausen/Approximation/Dual.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual maps, structural hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite SSet Topology
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen

section SameUniverses
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {Wd : Structure Cᵒᵖ} {V : Structure D} {Vd : Structure Dᵒᵖ}
  (hW : IsCompatibleDual W Wd)
  (hV : IsCompatibleDual V Vd) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hFd : IsExact Wd.cof Wd.weq Vd.cof Vd.weq F.op)
  (h : HasDualApproximationProperty W V Wd.cof.unop F)
  [V.weq.HasTwoOutOfThreeProperty]
  (Jd : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl Wd))
include hW hV hFd h Jd

/-- Dual approximation proves complete weakness of the unchanged original realization map. -/
@[colib_tag "COL-0308",
  colib_ref "quillen" "Quillen/Waldhausen/Approximation/Dual.lean:85-90" "adaptation"
    "Dual approximation proves weakness of the literal original delooping map"]
theorem deloopingMap_isWeakHomotopyEquivalence_of_dualApproximation :
    IsWeakHomotopyEquivalence (deloopingMap hF).hom := by
  let := hV.dual_saturated
  exact DualSConstruction.sSetMap_weak_of_dual hW hV hF hFd
    ((h.op hW hV).deloopingMap_isWeakHomotopyEquivalence_general hFd Jd)

/-- The actual original K-homomorphism is bijective in every connective degree. -/
theorem KMap_bijective_of_dualApproximation (n : ℕ) :
    Function.Bijective (KMap hF n) :=
  KMap_bijective_of_isWeakHomotopyEquivalence hF
    (deloopingMap_isWeakHomotopyEquivalence_of_dualApproximation hW hV hF hFd h Jd) n

/-- The dual approximation equivalence has exactly the original K-map as forward map. -/
@[colib_tag "COL-0308",
  colib_ref "quillen" "Quillen/Waldhausen/Approximation/Dual.lean:92-105" "adaptation"
    "The original canonical KMap is the equivalence in every connective degree"]
def KEquivOfDualApproximation (n : ℕ) : W.K n ≃* V.K n :=
  MulEquiv.ofBijective (KMap hF n)
    (KMap_bijective_of_dualApproximation hW hV hF hFd h Jd n)

/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem KEquivOfDualApproximation_coe (n : ℕ) :
    (↑(KEquivOfDualApproximation hW hV hF hFd h Jd n) : W.K n →* V.K n) = KMap hF n := rfl

end SameUniverses
end CategoryTheory.Waldhausen
