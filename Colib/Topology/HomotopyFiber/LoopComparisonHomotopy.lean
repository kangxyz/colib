/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.Equiv.InverseNaturality
public import Colib.Topology.HomotopyFiber.BasedHomotopySquareMap
public import Colib.Topology.HomotopyFiber.LoopPrefixBasepointNaturality

/-!
# Space-level naturality of the original inverse loop comparisons

The original forward prefix maps commute up to continuous homotopy with the
actual homotopy-fiber square. A specified path in the target fiber then compares
the two displayed prefix points. Cancelling the genuine loop/fiber homotopy
equivalences gives naturality of their existing inverses as a homotopy of maps,
without natural contractions or inference from homotopy groups.
-/

open Topology CategoryTheory

/-! Implementation source: `Quillen/Topology/HomotopyFiber/LoopComparisonHomotopy.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section

noncomputable section

open scoped Topology

universe u v u' v' w w'

namespace Topology.HomotopyFiber

variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
  {A : Type w} {A' : Type w'}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
  [TopologicalSpace A] [TopologicalSpace A']

/-- The actual forward square, transported along the entire specified fiber path. -/
def loopPrefixBasedSquarePathHomotopy {f : C(X, Y)} {f' : C(X', Y')}
    (u : C(X, X')) (v : C(Y, Y')) (H : (v.comp f).Homotopy (f'.comp u))
    (y : Y) (y' : Y') (h : v y = y')
    (z : HomotopyFiber f y) (z' : HomotopyFiber f' y')
    (q : Path (basedHomotopySquareMap u v H y y' h z) z') :
    ((loopPrefix f' z'.val.1 y' (toPath f' y' z')).comp
      (basedLoopMap v h)).Homotopy
    ((basedHomotopySquareMap u v H y y' h).comp
      (loopPrefix f z.val.1 y (toPath f y z))) := by
  subst y'
  exact ((loopPrefixPathHomotopy q).symm.compContinuousMap (basedLoopMap v rfl)).trans
    (loopPrefixHomotopySquare u v H z.val.1 y (toPath f y z))

/-- An actual comparison square induces a continuous homotopy for the unchanged
inverse loop comparisons. The change of displayed fiber point uses precisely the
square track followed by the image of the supplied source-basepoint path. -/
def loopComparisonNaturalityHomotopy [ContractibleSpace X] [ContractibleSpace X']
    {f : C(X, Y)} {f' : C(X', Y')}
    (u : C(X, X')) (v : C(Y, Y')) (H : (v.comp f).Homotopy (f'.comp u))
    (y : Y) (y' : Y') (h : v y = y')
    (c : C(A, HomotopyFiber f y)) (d : C(A', HomotopyFiber f' y')) (a : C(A, A'))
    (J : ((basedHomotopySquareMap u v H y y' h).comp c).Homotopy (d.comp a))
    (x : A) (x' : A') (p : Path (a x) x') :
    ((basedLoopMap v h).comp
      ((loopEquivOfContractibleSourcePath f (c x).val.1 y (toPath f y (c x))).invFun.comp
        c)).Homotopy
    (((loopEquivOfContractibleSourcePath f' (d x').val.1 y'
      (toPath f' y' (d x'))).invFun.comp d).comp a) := by
  let M := basedHomotopySquareMap u v H y y' h
  let q : Path (M (c x)) (d x') := (J.evalAt x).trans (p.map d.continuous)
  let E := loopEquivOfContractibleSourcePath f (c x).val.1 y (toPath f y (c x))
  let E' := loopEquivOfContractibleSourcePath f' (d x').val.1 y' (toPath f' y' (d x'))
  have F : (E'.toFun.comp (basedLoopMap v h)).Homotopy (M.comp E.toFun) :=
    (loopPrefixBasedSquarePathHomotopy u v H y y' h (c x) (d x') q).cast
      (congrArg (fun b ↦ b.comp (basedLoopMap v h))
        (loopPrefix_eq_forward f' (d x').val.1 y' (toPath f' y' (d x'))))
      (congrArg (fun b ↦ M.comp b)
        (loopPrefix_eq_forward f (c x).val.1 y (toPath f y (c x))))
  have G : ((basedLoopMap v h).comp E.invFun).Homotopy (E'.invFun.comp M) :=
    E.inverseNaturalityHomotopy E' (basedLoopMap v h) M F
  have K : (E'.invFun.comp (M.comp c)).Homotopy (E'.invFun.comp (d.comp a)) :=
    (ContinuousMap.Homotopy.refl E'.invFun).comp J
  exact (G.compContinuousMap c).trans K

end Topology.HomotopyFiber
