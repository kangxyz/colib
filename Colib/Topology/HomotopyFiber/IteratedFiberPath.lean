/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.ContractibleSourcePath
public import Colib.Topology.HomotopyFiber.ProjectionFibration
public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.VanishingTransport

/-!
# An iterated homotopy fiber with a specified endpoint path

The strict fiber of a homotopy-fiber projection is the actual fiber of a point map.
Its projection is already a genuine fibration. A specified path from the image of the source
point to the target basepoint therefore gives a loop-to-iterated-fiber homotopy equivalence.
The forward map retains that entire path as a prefix and stores a constant outer path.
The path removing the loop unit is explicit; the prefix is not assumed constant.

## Implementation provenance

Adapted from `Quillen/Topology/HomotopyFiber/IteratedFiberPath.lean` at Quillen
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u
namespace Topology.HomotopyFiber

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]
  (p : C(E, B)) (b : B) (x : E)

/-- Fixing the original projection coordinate leaves exactly the point-map homotopy fiber. -/
def strictProjectionFiberPointHomeomorph :
    {z : HomotopyFiber p b // projection p b z = x} ≃ₜ
      HomotopyFiber (ContinuousMap.const Unit (p x)) b where
  toFun z := ⟨((), z.1.1.2), z.1.2.1.trans (congrArg p z.2), z.1.2.2⟩
  invFun z := ⟨⟨(x, z.1.2), z.2⟩, rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact _root_.Prod.ext z.2.symm rfl
  right_inv z := by
    apply Subtype.ext
    exact _root_.Prod.ext (Subsingleton.elim _ _) rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The point-map comparison changes neither the path nor its parametrization. -/
@[simp] theorem strictProjectionFiberPointHomeomorph_path
    (z : {z : HomotopyFiber p b // projection p b z = x}) :
    (strictProjectionFiberPointHomeomorph p b x z).1.2 = z.1.1.2 := rfl

variable (γ : Path (p x) b)

/-- The actual loop equivalence, with the supplied endpoint path retained as a prefix. -/
def loopsToIteratedFiberPathEquiv : ContinuousMap.HomotopyEquiv
    (Path b b) (HomotopyFiber (projection p b) x) :=
  (loopEquivOfContractibleSourcePath (ContinuousMap.const Unit (p x)) () b γ).trans
    ((strictProjectionFiberPointHomeomorph p b x).symm.toHomotopyEquiv.trans
      (strictFiberHomotopyEquivOfLifting (projection p b)
        (projection_homotopyLiftingProperty p b) x))

/-- The inner source coordinate is the original specified source point. -/
@[simp] theorem loopsToIteratedFiberPathEquiv_source (δ : Path b b) :
    (loopsToIteratedFiberPathEquiv p b x γ δ).1.1.1.1 = x := rfl

/-- The whole specified endpoint path is prepended to the whole original loop. -/
@[simp] theorem loopsToIteratedFiberPathEquiv_innerPath (δ : Path b b) :
    (loopsToIteratedFiberPathEquiv p b x γ δ).1.1.1.2 = (γ.trans δ).toContinuousMap := by
  exact loopEquivOfContractibleSourcePath_path (ContinuousMap.const Unit (p x)) () b γ δ

/-- The outer path is literally constant at the displayed source point. -/
@[simp] theorem loopsToIteratedFiberPathEquiv_outerPath (δ : Path b b) :
    (loopsToIteratedFiberPathEquiv p b x γ δ).1.2 = ContinuousMap.const unitInterval x := rfl

/-- Removing the loop unit gives the exact basepoint track with the original endpoint path. -/
def loopsToIteratedFiberPathUnitPath :
    Path (loopsToIteratedFiberPathEquiv p b x γ (Path.refl b))
      (basepoint (projection p b) x (pointWithPath p x b γ) rfl) :=
  (loopEquivOfContractibleSourcePathUnitPath (ContinuousMap.const Unit (p x)) () b γ).map
    (((strictFiberHomotopyEquivOfLifting (projection p b)
      (projection_homotopyLiftingProperty p b) x).toFun).comp
      ((strictProjectionFiberPointHomeomorph p b x).symm :
        C(HomotopyFiber (ContinuousMap.const Unit (p x)) b,
          {z : HomotopyFiber p b // projection p b z = x}))).continuous

/-- The actual iterated fiber has the shifted target homotopy sets at every displayed point.
The intermediate loop basepoint is retained and corrected by the proved loop translation. -/
def iteratedFiberPiEquivOfPath (z : HomotopyFiber (projection p b) x) (k : ℕ) :
    HomotopyGroup.Pi k (HomotopyFiber (projection p b) x) z ≃
      HomotopyGroup.Pi (k + 1) B b := by
  let e := (loopsToIteratedFiberPathEquiv p b x γ).symm
  exact (Equiv.ofBijective (HomotopyGroup.map (N := Fin k) e.toFun (x := z) rfl)
    (homotopyGroupMap_bijective_of_homotopyEquiv e rfl k)).trans
      ((loopComponentHomotopyEquiv (e z) k).symm.trans (loopShiftEquiv (x := b) k).symm)

include γ in
/-- Vanishing in the next target degree kills every actual iterated-fiber homotopy set.
The supplied endpoint path is used only in the genuine loop equivalence above. -/
theorem subsingleton_iteratedFiber_of_succ (k : ℕ)
    (h : Subsingleton (HomotopyGroup.Pi (k + 1) B b))
    (z : HomotopyFiber (projection p b) x) :
    Subsingleton (HomotopyGroup.Pi k (HomotopyFiber (projection p b) x) z) := by
  let e := (loopsToIteratedFiberPathEquiv p b x γ).symm
  let := subsingleton_pi_loop_of_succ b k h (e z)
  exact (homotopyGroupMap_bijective_of_homotopyEquiv e rfl k).injective.subsingleton

end Topology.HomotopyFiber
