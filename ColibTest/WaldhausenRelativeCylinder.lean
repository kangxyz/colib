/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Colib.KTheory.Waldhausen.Iterated.LoopWeakEquivalence

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory SSet Topology
open scoped Simplicial Topology unitInterval

universe u

namespace WaldhausenRelativeCylinderTests

open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.Fibration CategoryTheory.Waldhausen.Fibration.RelativeRows
open CategoryTheory.Waldhausen.SmallWaldhausenCategory

variable {C : Type u} [SmallCategory C] (W : Structure C)

-- The lift retains the actual quotient-row functor, not an equivalent replacement.
example {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    relativeTimeRow W τ ⋙ RelativeRows.forget (AllWeak.nested W) n =
      suspensionRow W (relativeTime τ) := rfl

example {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    IsExact W.cof W.weq (RelativeRows.waldhausenStructure (AllWeak.nested W) n).cof
      (RelativeRows.waldhausenStructure (AllWeak.nested W) n).weq (relativeTimeRow W τ) :=
  relativeTimeRow_exact W τ

example {m n : SimplexCategory} (α : m ⟶ n) (τ : n ⟶ ⦋1⦌) :
    relativeTimeRow W τ ⋙ RelativeRows.reindex (AllWeak.nested W) α =
      relativeTimeRow W (α ≫ τ) := relativeTimeRow_reindex W α τ

example (n : SimplexCategory) :
    relativeTimeRow W (n.const ⦋1⦌ 0) =
      (Functor.const C).obj (RelativeRows.zero (AllWeak.nested W) n) :=
  relativeTimeRow_zero W n

example (n : SimplexCategory) :
    relativeTimeRow W (n.const ⦋1⦌ 1) = fiber (AllWeak.nested W) n :=
  relativeTimeRow_one W n

-- Both literal faces and the entire simplicial homotopy use the original maps.
example : SSet.ι₀ ≫ relativeCylinder W = SSet.const (totalZeroVertex (AllWeak.nested W)) :=
  relativeCylinder_zero W

example : SSet.ι₁ ≫ relativeCylinder W = totalFiberInclusion (AllWeak.nested W) :=
  relativeCylinder_one W

example : (relativeHomotopy W).h = relativeCylinder W := rfl

example : relativeCylinder W ≫ relativeTail W = suspensionCylinder W :=
  relativeCylinder_tail W

example : relativeProjection W = (SSet.toTop.map (relativeTail W)).hom :=
  relativeProjection_eq W

-- This tests every time, rather than merely comparing endpoints.
example (t : unitInterval) (x : W.Delooping) :
    relativeProjection W (relativeTopHomotopy W (t, x)) =
      realizationSimplicialHomotopy (suspensionHomotopy W) (t, x) :=
  relativeTopHomotopy_tail W t x

example :
    HomotopyFiber.cylinderLoop (relativeProjection W) (doubleBasepoint W)
      (totalBasepoint (AllWeak.nested W)) (relativeProjection_point W)
      (SSet.toTop.map (totalFiberInclusion (AllWeak.nested W))).hom
      (relativeProjection_fiberInclusion W) (relativeTopHomotopy W) = loopStructureMap W :=
  cylinderLoop_eq_loopStructureMap W

-- Test both coordinates of the original relative fiber homeomorphism.
example (z : HomotopyFiber (totalTailMap (AllWeak.nested W))
    (ordinaryTotalBasepoint (acyclicStructure (AllWeak.nested W)))) :
    (relativeFiberHomeomorph W z).1.1 = z.1.1 := relativeFiberHomeomorph_source W z

example (z : HomotopyFiber (totalTailMap (AllWeak.nested W))
    (ordinaryTotalBasepoint (acyclicStructure (AllWeak.nested W)))) (t : unitInterval) :
    (relativeFiberHomeomorph W z).1.2 t = AllWeak.ordinaryTotalInclusionMap W (z.1.2 t) := rfl

example :
    (relativeFiberHomeomorph W : C(_, _)).comp (totalTailFiberComparison (AllWeak.nested W)) =
      HomotopyFiber.cylinderStrictLift (relativeProjection W) (doubleBasepoint W)
        (SSet.toTop.map (totalFiberInclusion (AllWeak.nested W))).hom
        (relativeProjection_fiberInclusion W) := relativeFiberHomeomorph_comparison W

example : IsWeakHomotopyEquivalence
    (HomotopyFiber.cylinderStrictLift (relativeProjection W) (doubleBasepoint W)
      (SSet.toTop.map (totalFiberInclusion (AllWeak.nested W))).hom
      (relativeProjection_fiberInclusion W)) := relativeStrictComparison_weak W

-- The native displayed-cylinder homotopy retains its entire remaining path.
example (s t : unitInterval) (x : W.Delooping) :
    (HomotopyFiber.cylinderFiberHomotopy (relativeProjection W) (doubleBasepoint W)
      (totalBasepoint (AllWeak.nested W)) (relativeProjection_point W)
      (SSet.toTop.map (totalFiberInclusion (AllWeak.nested W))).hom
      (relativeProjection_fiberInclusion W) (relativeTopHomotopy W) (s, x)).1.2 t =
      relativeProjection W
        (relativeTopHomotopy W (unitInterval.symm (unitInterval.symm s * unitInterval.symm t),
          x)) := rfl

-- Reuse the actual stage-zero map on the original category, without AsSmall transport.
example : IsWeakHomotopyEquivalence (loopStructureMap W) := by
  let B : WideSubcategory preservesZero.{u} := ⟨{ Obj := C, waldhausen := W }⟩
  simpa only [stageLoopMap_zero] using stageLoopMap_weak 0 B

example : Function.Bijective (HomotopyGroup.map (N := Fin 0) (loopStructureMap W)
    (loopStructureMap_basepoint W)) := loopStructureMap_bijective W 0

example (n : ℕ) : Function.Bijective (degreeRaisingMap W n) := degreeRaisingMap_bijective W n

example (n : ℕ) : (degreeRaisingEquiv W n).toMonoidHom = degreeRaisingMap W n :=
  degreeRaisingEquiv_toMonoidHom W n

example (n : ℕ) (a : W.K n) : degreeRaisingEquiv W n a = degreeRaisingMap W n a := rfl

example : W.K 0 ≃* HomotopyGroup.Pi 2 (doubleDelooping W) (doubleBasepoint W) :=
  degreeRaisingEquiv W 0

end WaldhausenRelativeCylinderTests
