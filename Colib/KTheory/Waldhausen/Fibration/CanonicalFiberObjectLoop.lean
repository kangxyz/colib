/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberMap
public import Colib.KTheory.Waldhausen.GrothendieckComparison.ObjectNaturality
public import Colib.Topology.HomotopyFiber.Loop

/-!
# Actual acyclic object loops and their canonical-fiber transpose

The source is the original fine object loop. The stored path is the full reversed
zero-to-acyclic-inclusion nullhomotopy, with independent loop and fiber parameters.
The existing loop/fiber homeomorphism transposes these parameters without another reversal.
No zero-morphism, canonical-fiber weakness, cylinder or fibration hypothesis is needed.

Implementation provenance: selected declarations from Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`:
* `Quillen/Waldhausen/Fibration/CanonicalFiberObjectLoop.lean`, lines 32–50:
  `canonicalFiberObjectLoop`, `_projection`, `_path`.
* `Quillen/Waldhausen/Fibration/CofiberPrismLeftPrefix.lean`, lines 28–49:
  `canonicalFiberObjectLoopTranspose`, `_source`, `_path`, `_one`.

This selection does not include the remaining weak-object/transformation tracks or the
cofiber-prism cube law from either source file. Objects, parameters and universes are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Topology
open scoped Topology
universe u v
namespace CategoryTheory.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The original acyclic object loop maps through the actual canonical homotopy-fiber map. -/
def canonicalFiberObjectLoop (X : AcyclicCategory N) :
    Path (HomotopyFiber.basepoint (changeWeakMap N) N.coarse.kBasepoint V.kBasepoint
      (changeWeakMap_basepoint N))
      (HomotopyFiber.basepoint (changeWeakMap N) N.coarse.kBasepoint V.kBasepoint
        (changeWeakMap_basepoint N)) :=
  basedLoopMap (canonicalFiberMap N) (canonicalFiberMap_basepoint N)
    ((acyclicStructure N).kZeroObjectLoop X)

/-- Its original source coordinate is the unchanged fine object loop. -/
theorem canonicalFiberObjectLoop_projection (X : AcyclicCategory N) (t : unitInterval) :
    (canonicalFiberObjectLoop N X t).val.1 = V.kZeroObjectLoop X.obj t := by
  exact congrArg (fun p : Path V.kBasepoint V.kBasepoint => p t)
    (deloopingMap_kZeroObjectLoop (acyclicInclusion_exact N) rfl X)

/-- Its independent fiber coordinate retains the full original reversed zero track. -/
theorem canonicalFiberObjectLoop_path (X : AcyclicCategory N) (t s : unitInterval) :
    (canonicalFiberObjectLoop N X t).val.2 s =
      acyclicNullhomotopy N (s, (acyclicStructure N).kZeroObjectLoop X t) := rfl

/-- Transpose the original canonical-fiber object loop using the existing exact homeomorphism. -/
def canonicalFiberObjectLoopTranspose (X : AcyclicCategory N) :
    HomotopyFiber (basedLoopMap (changeWeakMap N) (changeWeakMap_basepoint N))
      (Path.refl N.coarse.kBasepoint) :=
  (HomotopyFiber.loopFiberHomeomorph (changeWeakMap N) (changeWeakMap_basepoint N)).symm
    (canonicalFiberObjectLoop N X)

/-- The original fine object loop is unchanged by this prescribed coordinate transpose. -/
theorem canonicalFiberObjectLoopTranspose_source (X : AcyclicCategory N) :
    (canonicalFiberObjectLoopTranspose N X).val.1 = V.kZeroObjectLoop X.obj := by
  ext t
  exact canonicalFiberObjectLoop_projection N X t

/-- The stored path retains both original loop and reversed canonical-fiber coordinates. -/
theorem canonicalFiberObjectLoopTranspose_path (X : AcyclicCategory N) (s t : unitInterval) :
    (canonicalFiberObjectLoopTranspose N X).val.2 s t =
      (canonicalFiberObjectLoop N X t).val.2 s := rfl

/-- The transposed target is exactly the actual constant loop. -/
theorem canonicalFiberObjectLoopTranspose_one (X : AcyclicCategory N) :
    (canonicalFiberObjectLoopTranspose N X).val.2 1 = Path.refl N.coarse.kBasepoint :=
  (canonicalFiberObjectLoopTranspose N X).property.2

end CategoryTheory.Waldhausen.Fibration
