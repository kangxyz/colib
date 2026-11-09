/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import StacksFrontier.RingTheory.Koszul.TorComparison.QuotientTor
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.RingTheory.Sequence.Regular.Basic

/-!
# Tor of two quotients cut out by compatible regular sequences

Degree-zero Tor is the literal quotient by the sum of the two ideals. If a regular
sequence remains regular after an earlier sequence, the two quotient rings have no
positive Tor. The proof uses the native quotient Koszul resolution and the native
regular-append criterion, without a new resolution or module model.

These ring-level suppliers are used when the two original middle diagonals are paired
first in the finite-correspondence triple-Tor comparison. They require no field,
Noetherianity, finite-dimensionality, or choice of geometric charts.

References: the degree-zero derived tensor identity and quotient tensor product from
Mathlib; Stacks 062F and 062E for regular and Koszul-regular sequences, as implemented
by the pinned native quotient Tor comparison. This is an algebraic consequence of
those native statements, not a new form of cycle associativity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open RingTheory.Sequence
open scoped TensorProduct

universe u

namespace CategoryTheory

/-- The native degree-zero Tor of two quotient rings is the quotient by their sum. -/
def torZeroQuotientQuotientIso (A : Type u) [CommRing A] (I J : Ideal A) :
    (((Tor (ModuleCat A) 0).obj (ModuleCat.of A (A ⧸ I))).obj
      (ModuleCat.of A (A ⧸ J))) ≅ ModuleCat.of A (A ⧸ I ⊔ J) := by
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A ⧸ I) J).symm
  let e' := DoubleQuot.quotQuotEquivQuotSupₐ A I J
  exact (Functor.leftDerivedZeroIsoSelf (tensorLeft (ModuleCat.of A (A ⧸ I)))).app
      (ModuleCat.of A (A ⧸ J)) ≪≫
    (e.toLinearEquiv.restrictScalars A).toModuleIso ≪≫ e'.toLinearEquiv.toModuleIso

end CategoryTheory

namespace Koszul

/-- Appending regular equations makes the two original equation quotients Tor independent. -/
theorem isZero_tor_quotients_of_regular_append (A : Type u) [CommRing A]
    (t s : List A) (hs : IsRegular A s) (hts : IsRegular A (t ++ s))
    (I J : Ideal A) (hI : I = Ideal.ofList t) (hJ : J = Ideal.ofList s)
    (n : ℕ) (hn : n ≠ 0) :
    IsZero (((Tor (ModuleCat A) n).obj (ModuleCat.of A (A ⧸ J))).obj
      (ModuleCat.of A (A ⧸ I))) := by
  have hw := ((RingTheory.Sequence.isWeaklyRegular_append_iff A t s).mp
    hts.toIsWeaklyRegular).2
  have hweak : IsWeaklyRegular (A ⧸ I) s := by
    subst I
    have htop : (Ideal.ofList t • (⊤ : Submodule A A)) = Ideal.ofList t := by
      change Ideal.ofList t * ⊤ = Ideal.ofList t
      exact Ideal.mul_top _
    exact ((Submodule.quotEquivOfEq _ _ htop).isWeaklyRegular_congr s).mp hw
  let e := Koszul.torIsoHomologySeqComplexTensorOfIsRegular s.get
    (by simpa only [List.ofFn_get] using hs) J
    (hJ.trans (by rw [← Ideal.ofList_ofFn, List.ofFn_get])) (A ⧸ I) n
  exact IsZero.of_iso
    ((Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular.1
      (by simpa only [List.ofFn_get] using hweak)) n hn) e

end Koszul

