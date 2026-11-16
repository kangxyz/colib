/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Covering.Pullback
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransport

/-!
# Simply connected pullbacks of coverings

A map inducing a fundamental-group isomorphism pulls a simply connected
covering back to a simply connected covering of the original source. Its
points remain the original matching pairs. No comparison homeomorphism or
homological Whitehead theorem is used.
-/

@[expose] public section

noncomputable section
universe u v w
open CategoryTheory
open scoped Topology

namespace Topology.Covering.Pullback

variable {X : Type u} {Y : Type v} {E : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]
  [PathConnectedSpace X] [SimplyConnectedSpace E]
  (f : C(X, Y)) (q : C(E, Y)) (hq : IsCoveringMap q)
  (z₀ : Space f q)

omit [PathConnectedSpace X] [SimplyConnectedSpace E] in
private theorem piOne_injective_iff_at_endpoint {x : X} {y : Y} (h : f x = y) :
    Function.Injective (HomotopyGroup.piMap 0 f h) ↔
      Function.Injective (HomotopyGroup.map (N := Fin 1) f (x := x) rfl) := by
  cases h
  rfl

include hq in
/-- The actual pullback is simply connected if the original map is bijective
on the fundamental group at one specified matching pair. -/
theorem simplyConnectedSpace
    (hf : Function.Bijective (HomotopyGroup.piMap 0 f z₀.property)) :
    SimplyConnectedSpace (Space f q) := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨pathConnectedSpace f q hq z₀ hf.surjective, ?_⟩
  intro z p
  have hinj₀ : Function.Injective (HomotopyGroup.map (N := Fin 1) f
      (x := z₀.val.1) rfl) :=
    (piOne_injective_iff_at_endpoint f z₀.property).mp hf.injective
  let γ := PathConnectedSpace.somePath z₀.val.1 z.val.1
  have hinj₁ := (homotopyGroupMap_injective_iff_of_path f γ 1).mp hinj₀
  have hinj : Function.Injective (HomotopyGroup.piMap 0 f z.property) :=
    (piOne_injective_iff_at_endpoint f z.property).mpr hinj₁
  have hsub : Subsingleton (HomotopyGroup.Pi 1 (Space f q) z) := by
    refine ⟨fun a b ↦ ?_⟩
    apply (piOneKernelEquiv f q hq z).injective
    apply Subtype.ext
    apply hinj
    exact ((piOneKernelEquiv f q hq z a).property).trans
      ((piOneKernelEquiv f q hq z b).property).symm
  apply Path.Homotopic.Quotient.eq.mp
  have h : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (Path.refl z)) :=
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm.injective (hsub.elim _ _)
  exact congrArg End.asHom h

end Topology.Covering.Pullback
