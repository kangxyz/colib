/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.LoopPrefixNaturality
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Actual homotopy-fiber paths in the fundamental groupoid

The stored path coordinate makes every path in the homotopy fiber a genuine
commuting square of fundamental-groupoid arrows. The formula preserves the
actual source projection and the entire stored endpoint paths.
-/

open Topology CategoryTheory

/-! Implementation source: `Quillen/Topology/HomotopyFiber/PathClass.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and original proofs are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory
open scoped Topology
namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (y : Y)

/-- A fiber path makes its projected source path commute with the two stored paths. -/
theorem pathClass_square {z w : HomotopyFiber f y} (p : Path z w) :
    (FundamentalGroupoid.map f).map
      ((FundamentalGroupoid.map (projection f y)).map (Path.Homotopic.Quotient.mk p)) ≫
        Path.Homotopic.Quotient.mk (toPath f y w) =
      Path.Homotopic.Quotient.mk (toPath f y z) := by
  have h := (FundamentalGroupoidFunctor.homotopicMapsNatIso
    (projectionNullhomotopy f y)).naturality (Path.Homotopic.Quotient.mk p)
  have hc : (FundamentalGroupoid.map (ContinuousMap.const (HomotopyFiber f y) y)).map
      (Path.Homotopic.Quotient.mk p) = 𝟙 (FundamentalGroupoid.mk y) := by
    change Path.Homotopic.Quotient.mk (p.map continuous_const) =
      Path.Homotopic.Quotient.mk (Path.refl y)
    rfl
  rw [hc] at h
  exact h.trans (Category.comp_id _)

/-- The original inverse loop comparison has the class forced by any displayed source path. -/
theorem loopInverse_pathClass [ContractibleSpace X] (x : X) (γ : Path (f x) y)
    (z : HomotopyFiber f y) (p : Path x z.val.1) :
    Path.Homotopic.Quotient.mk ((loopEquivOfContractibleSourcePath f x y γ).invFun z) =
      Path.Homotopic.Quotient.mk (γ.symm.trans ((p.map f.continuous).trans (toPath f y z))) := by
  let e := loopEquivOfContractibleSourcePath f x y γ
  let β := (Classical.choice e.right_inv).evalAt z
  have h := pathClass_square f y β
  have hp : (FundamentalGroupoid.map (projection f y)).map
      (Path.Homotopic.Quotient.mk β) = Path.Homotopic.Quotient.mk p :=
    @Subsingleton.elim (Path.Homotopic.Quotient x z.val.1) inferInstance _ _
  rw [hp] at h
  have he : toPath f y (e.toFun (e.invFun z)) = γ.trans (e.invFun z) := by
    ext t
    exact congrArg (fun q : C(unitInterval, Y) ↦ q t)
      (loopEquivOfContractibleSourcePath_path f x y γ (e.invFun z))
  change _ = Path.Homotopic.Quotient.mk (toPath f y (e.toFun (e.invFun z))) at h
  rw [he] at h
  apply (cancel_epi (C := FundamentalGroupoid Y) (Path.Homotopic.Quotient.mk γ :
    FundamentalGroupoid.mk (f x) ⟶ FundamentalGroupoid.mk y)).1
  change Path.Homotopic.Quotient.mk (γ.trans (e.invFun z)) = _
  rw [← h]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  change (Path.Homotopic.Quotient.mk (p.map f.continuous)).trans
    (Path.Homotopic.Quotient.mk (toPath f y z)) =
      (Path.Homotopic.Quotient.mk γ).trans
        ((Path.Homotopic.Quotient.mk γ).symm.trans
          ((Path.Homotopic.Quotient.mk (p.map f.continuous)).trans
            (Path.Homotopic.Quotient.mk (toPath f y z))))
  erw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.refl_trans]

end Topology.HomotopyFiber
