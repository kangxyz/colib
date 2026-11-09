/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.ExactModelEquivalence
public import Colib.KTheory.Waldhausen.Iterated.SmallModelComparison
public import Colib.KTheory.Waldhausen.Iterated.SmallModelBridge

/-!
# Exact forward formulas for equivalences of native small models

The K-equivalence uses the actual forward exact functor. Zero-space and stable formulas
identify that same map, including degree zero. The original-universe target comparison
uses AsSmall explicitly; no mixed-universe raw K-map is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology
universe u v
namespace CategoryTheory.Waldhausen.IteratedS.ExactModelEquivalence
open SmallWaldhausenCategory Topology.LoopPrespectrum
variable {V W : WideSubcategory preservesZero.{u}} (e : V.obj.Obj ≌ W.obj.Obj)
  (hF : IsExact V.obj.waldhausen.cof V.obj.waldhausen.weq
    W.obj.waldhausen.cof W.obj.waldhausen.weq e.functor)
  (hG : IsExact W.obj.waldhausen.cof W.obj.waldhausen.weq
    V.obj.waldhausen.cof V.obj.waldhausen.weq e.inverse)
  (h0 : e.functor.obj V.obj.waldhausen.zero = W.obj.waldhausen.zero)

/-- The all-degree equivalence retains the actual canonical forward K-map. -/
def kEquiv (n : ℕ) : V.obj.waldhausen.K n ≃* W.obj.waldhausen.K n :=
  KEquivOfExactEquivalence e hF hG n

/-- In every degree, including zero, the forward map is the original exact map. -/
theorem kEquiv_apply (n : ℕ) (a : V.obj.waldhausen.K n) :
    kEquiv e hF hG n a = KMap hF n a := rfl

/-- The exact forward K-map agrees with the unchanged forward spectrum on the zero space. -/
theorem kEquiv_zeroSpace (n : ℕ) (a : V.obj.waldhausen.K n) :
    zeroSpaceHomotopyEquiv W n (kEquiv e hF hG n a) =
      HomotopyGroup.map ((prespectrumMap (forward e hF h0)).map 0)
        ((prespectrumMap (forward e hF h0)).map_point 0) (zeroSpaceHomotopyEquiv V n a) :=
  smallModelZeroSpace_naturality (forward e hF h0) n a

/-- The exact forward K-map agrees with the unchanged forward map on actual stable groups. -/
theorem kEquiv_stable (n : ℕ) (a : V.obj.waldhausen.K n) :
    smallModelKStableEquiv W n (Additive.ofMul (kEquiv e hF hG n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (prespectrumMap (forward e hF h0))
        (smallModelKStableEquiv V n (Additive.ofMul a)) :=
  smallModelKStableEquiv_naturality (forward e hF h0) n a

section OriginalTarget
variable {C : Type u} [Category.{v} C] (T : Structure C)
  {A : WideSubcategory preservesZero.{max u v}}
  (e : A.obj.Obj ≌ AsSmall.{0} C)
  (hF : IsExact A.obj.waldhausen.cof A.obj.waldhausen.weq
    T.asSmall.cof T.asSmall.weq e.functor)
  (hG : IsExact T.asSmall.cof T.asSmall.weq
    A.obj.waldhausen.cof A.obj.waldhausen.weq e.inverse)
  (h0 : e.functor.obj A.obj.waldhausen.zero = AsSmall.up.obj T.zero)

/-- A direct-small source compares to the original target through its actual AsSmall lift. -/
def originalTargetKEquiv (n : ℕ) : A.obj.waldhausen.K n ≃* T.K n :=
  (kEquiv (W := asSmallCategory T) e hF hG n).trans (T.asSmallKEquiv n).symm

/-- The formula uses the lifted canonical map, never an unavailable mixed-universe K-map. -/
theorem originalTargetKEquiv_apply (n : ℕ) (a : A.obj.waldhausen.K n) :
    originalTargetKEquiv T e hF hG n a = (T.asSmallKEquiv n).symm (KMap hF n a) := rfl

/-- The target zero-space comparison cancels precisely the actual AsSmall equivalence. -/
theorem originalTargetKEquiv_zeroSpace (n : ℕ) (a : A.obj.waldhausen.K n) :
    originalZeroSpaceEquiv T n (originalTargetKEquiv T e hF hG n a) =
      HomotopyGroup.map ((prespectrumMap (forward (W := asSmallCategory T) e hF h0)).map 0)
        ((prespectrumMap (forward (W := asSmallCategory T) e hF h0)).map_point 0)
        (zeroSpaceHomotopyEquiv A n a) := by
  change zeroSpaceHomotopyEquiv (asSmallCategory T) n
    (T.asSmallKEquiv n ((T.asSmallKEquiv n).symm (KMap hF n a))) = _
  rw [MulEquiv.apply_symm_apply]
  exact smallModelZeroSpace_naturality (forward (W := asSmallCategory T) e hF h0) n a

/-- The original target stable comparison factors through the identical lifted forward map. -/
theorem originalTargetKEquiv_stable (n : ℕ) (a : A.obj.waldhausen.K n) :
    originalKStableEquiv T n (Additive.ofMul (originalTargetKEquiv T e hF hG n a)) =
      (stableHomotopyFunctor (n : ℤ)).map
        (prespectrumMap (forward (W := asSmallCategory T) e hF h0))
        (smallModelKStableEquiv A n (Additive.ofMul a)) := by
  change smallModelKStableEquiv (asSmallCategory T) n
    (Additive.ofMul (T.asSmallKEquiv n ((T.asSmallKEquiv n).symm (KMap hF n a)))) = _
  rw [MulEquiv.apply_symm_apply]
  exact smallModelKStableEquiv_naturality (forward (W := asSmallCategory T) e hF h0) n a

end OriginalTarget
end CategoryTheory.Waldhausen.IteratedS.ExactModelEquivalence

attribute [colib_tag "COL-0357",
  colib_ref "Waldhausen1985" "Section 1.3, Proposition 1.3.1, pp. 330-331" "background"
    "Actual exact-functor maps and weak-natural-transformation invariance"]
  CategoryTheory.Waldhausen.IteratedS.ExactModelEquivalence.kEquiv
  CategoryTheory.Waldhausen.IteratedS.ExactModelEquivalence.kEquiv_zeroSpace
  CategoryTheory.Waldhausen.IteratedS.ExactModelEquivalence.kEquiv_stable
  CategoryTheory.Waldhausen.IteratedS.ExactModelEquivalence.originalTargetKEquiv
  CategoryTheory.Waldhausen.IteratedS.ExactModelEquivalence.originalTargetKEquiv_zeroSpace
  CategoryTheory.Waldhausen.IteratedS.ExactModelEquivalence.originalTargetKEquiv_stable
