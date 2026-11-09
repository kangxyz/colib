/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Waldhausen.Iterated.ExactModelComparison
import Colib.KTheory.Waldhausen.Iterated.SmallModelBridge
import Colib.KTheory.Waldhausen.Iterated.SmallModelComparison

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS Topology
open scoped unitInterval

noncomputable section

namespace SmallModelEquivalenceTest

-- An indiscrete category with two distinct zero objects. Its K-groups are not claimed nonzero.
inductive TwoZero | first | second
  deriving DecidableEq

instance : SmallCategory TwoZero where
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

instance (X Y : TwoZero) : Unique (X ⟶ Y) := inferInstanceAs (Unique PUnit)

instance {X Y : TwoZero} (f : X ⟶ Y) : IsIso f :=
  ⟨⟨PUnit.unit, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩

theorem zeroProof (X : TwoZero) : IsZero X :=
  ⟨fun _ => ⟨inferInstance⟩, fun _ => ⟨inferInstance⟩⟩

def waldhausen : Structure TwoZero where
  zero := .first
  isZero := zeroProof _
  cof := ⊤
  weq := ⊤
  cof_multiplicative := inferInstance
  weq_multiplicative := inferInstance
  cof_iso := by intro X Y f h; trivial
  weq_iso := by intro X Y f h; trivial
  cof_zero _ := trivial
  pushout_exists i f _ :=
    ⟨.first, PUnit.unit, PUnit.unit, IsPushout.of_horiz_isIso ⟨Subsingleton.elim _ _⟩⟩
  cof_pushout _ _ := trivial
  gluing _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := trivial

def model : WideSubcategory SmallWaldhausenCategory.preservesZero :=
  ⟨⟨TwoZero, waldhausen⟩⟩

-- The forward functor is identity; the actual chosen inverse is constant at the other zero.
def equivalence : TwoZero ≌ TwoZero where
  functor := 𝟭 _
  inverse := (Functor.const _).obj .second
  unitIso := NatIso.ofComponents
    (fun _ => ⟨PUnit.unit, PUnit.unit, Subsingleton.elim _ _, Subsingleton.elim _ _⟩)
    (by intros; exact Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents
    (fun _ => ⟨PUnit.unit, PUnit.unit, Subsingleton.elim _ _, Subsingleton.elim _ _⟩)
    (by intros; exact Subsingleton.elim _ _)

theorem inverse_exact : IsExact waldhausen.cof waldhausen.weq
    waldhausen.cof waldhausen.weq equivalence.inverse where
  zero _ := zeroProof _
  cofibration _ _ := trivial
  weak _ _ := trivial
  pushout _ _ := IsPushout.of_horiz_isIso ⟨Subsingleton.elim _ _⟩

example : equivalence.inverse.obj waldhausen.zero ≠ waldhausen.zero := by
  intro h
  cases h

example : (ExactModelEquivalence.backward (V := model) (W := model)
    equivalence inverse_exact).hom.toFunctor.obj waldhausen.zero = waldhausen.zero :=
  (ExactModelEquivalence.backward (V := model) (W := model) equivalence inverse_exact).property

example : LoopPrespectrum.Homotopy
    (prespectrumMap (ExactModelEquivalence.forward (V := model) (W := model)
      equivalence (IsExact.id _ _) rfl) ≫
      prespectrumMap (ExactModelEquivalence.backward (V := model) (W := model) equivalence inverse_exact))
    (𝟙 (prespectrum model)) :=
  ExactModelEquivalence.leftHomotopy (V := model) (W := model) equivalence (IsExact.id _ _) inverse_exact rfl

example : LoopPrespectrum.Homotopy
    (prespectrumMap (ExactModelEquivalence.backward (V := model) (W := model)
      equivalence inverse_exact) ≫
      prespectrumMap (ExactModelEquivalence.forward (V := model) (W := model) equivalence (IsExact.id _ _) rfl))
    (𝟙 (prespectrum model)) :=
  ExactModelEquivalence.rightHomotopy (V := model) (W := model) equivalence (IsExact.id _ _) inverse_exact rfl

example (n : ℕ) : ContinuousMap.HomotopyEquiv
    ((prespectrum model).space n) ((prespectrum model).space n) :=
  ExactModelEquivalence.levelHomotopyEquiv (V := model) (W := model)
    equivalence (IsExact.id _ _) inverse_exact rfl n

#print axioms ExactModelEquivalence.isStableEquivalence
#print axioms smallModelPrespectrumIso_naturality
#print axioms smallModelKStableEquiv_naturality

section General
universe u
variable {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
  (e : V.obj.Obj ≌ W.obj.Obj)
  (hF : IsExact V.obj.waldhausen.cof V.obj.waldhausen.weq
    W.obj.waldhausen.cof W.obj.waldhausen.weq e.functor)
  (hG : IsExact W.obj.waldhausen.cof W.obj.waldhausen.weq
    V.obj.waldhausen.cof V.obj.waldhausen.weq e.inverse)
  (h0 : e.functor.obj V.obj.waldhausen.zero = W.obj.waldhausen.zero)

example : (ExactModelEquivalence.forward e hF h0).hom.toFunctor = e.functor := rfl

example (n : ℕ) (a : V.obj.waldhausen.K n) :
    ExactModelEquivalence.kEquiv e hF hG n a = KMap hF n a := rfl

example (a : V.obj.waldhausen.K 0) :
    zeroSpaceHomotopyEquiv W 0 (ExactModelEquivalence.kEquiv e hF hG 0 a) =
      HomotopyGroup.map ((prespectrumMap (ExactModelEquivalence.forward e hF h0)).map 0)
        ((prespectrumMap (ExactModelEquivalence.forward e hF h0)).map_point 0)
        (zeroSpaceHomotopyEquiv V 0 a) :=
  ExactModelEquivalence.kEquiv_zeroSpace e hF hG h0 0 a

example (n : ℕ) (s t : unitInterval) (x : (prespectrum V).space n) :
    (ExactModelEquivalence.leftHomotopy e hF hG h0).level (n+1)
      (s, (prespectrum V).structureMap n x t) =
    (prespectrum V).structureMap n
      ((ExactModelEquivalence.leftHomotopy e hF hG h0).level n (s, x)) t :=
  ExactModelEquivalence.leftHomotopy_comm e hF hG h0 n s t x

example (n : ℕ) (s t : unitInterval) (x : (prespectrum W).space n) :
    (ExactModelEquivalence.rightHomotopy e hF hG h0).level (n+1)
      (s, (prespectrum W).structureMap n x t) =
    (prespectrum W).structureMap n
      ((ExactModelEquivalence.rightHomotopy e hF hG h0).level n (s, x)) t :=
  ExactModelEquivalence.rightHomotopy_comm e hF hG h0 n s t x

example (n : ℕ) (a : V.obj.waldhausen.K n) :
    smallModelKStableEquiv W n (Additive.ofMul (ExactModelEquivalence.kEquiv e hF hG n a)) =
      (LoopPrespectrum.stableHomotopyFunctor (n : ℤ)).map
        (prespectrumMap (ExactModelEquivalence.forward e hF h0))
        (smallModelKStableEquiv V n (Additive.ofMul a)) :=
  ExactModelEquivalence.kEquiv_stable e hF hG h0 n a

end General

section OriginalTarget
universe u v
variable {C : Type u} [Category.{v} C] (T : Structure C)
  {A : WideSubcategory SmallWaldhausenCategory.preservesZero.{max u v}}
  (e : A.obj.Obj ≌ AsSmall.{0} C)
  (hF : IsExact A.obj.waldhausen.cof A.obj.waldhausen.weq
    T.asSmall.cof T.asSmall.weq e.functor)
  (hG : IsExact T.asSmall.cof T.asSmall.weq
    A.obj.waldhausen.cof A.obj.waldhausen.weq e.inverse)
  (h0 : e.functor.obj A.obj.waldhausen.zero = AsSmall.up.obj T.zero)

example (n : ℕ) (a : A.obj.waldhausen.K n) :
    ExactModelEquivalence.originalTargetKEquiv T e hF hG n a =
      (T.asSmallKEquiv n).symm (KMap hF n a) := rfl

example (a : A.obj.waldhausen.K 0) :
    originalKStableEquiv T 0
      (Additive.ofMul (ExactModelEquivalence.originalTargetKEquiv T e hF hG 0 a)) =
    (LoopPrespectrum.stableHomotopyFunctor (0 : ℤ)).map
      (prespectrumMap (ExactModelEquivalence.forward (W := asSmallCategory T) e hF h0))
      (smallModelKStableEquiv A 0 (Additive.ofMul a)) :=
  ExactModelEquivalence.originalTargetKEquiv_stable T e hF hG h0 0 a

end OriginalTarget
#print axioms ExactModelEquivalence.originalTargetKEquiv_stable
end SmallModelEquivalenceTest
