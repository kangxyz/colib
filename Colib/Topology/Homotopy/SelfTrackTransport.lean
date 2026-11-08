/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-! # Evaluation transport of an actual continuous self-homotopy

The whole original homotopy supplies its own conjugacy square along the given path.
This construction is generic in two independent spaces and precedes prespectra.
Implementation source: `Quillen/Topology/Prespectrum/SelfTrackHomotopyClass.lean`,
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`, the first transport theorem.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology
universe u v
namespace Topology

/-- Evaluation of an actual self-homotopy is conjugate along its original image path. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackHomotopyClass.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem selfHomotopy_eval_transport {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)} (H : f.Homotopy f)
    {x₀ x₁ : X} (β : Path x₀ x₁) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath (β.map f.continuous)
        (FundamentalGroup.fromPath ⟦H.evalAt x₀⟧ : FundamentalGroup Y (f x₀)) =
      (FundamentalGroup.fromPath ⟦H.evalAt x₁⟧ : FundamentalGroup Y (f x₁)) := by
  let c : FundamentalGroupoid.mk (f x₀) ⟶ FundamentalGroupoid.mk (f x₁) :=
    ⟦β.map f.continuous⟧
  let a : FundamentalGroup Y (f x₀) := FundamentalGroup.fromPath ⟦H.evalAt x₀⟧
  let b : FundamentalGroup Y (f x₁) := FundamentalGroup.fromPath ⟦H.evalAt x₁⟧
  have hn : c ≫ b.asHom = a.asHom ≫ c :=
    (FundamentalGroupoidFunctor.homotopicMapsNatIso H).naturality
      (⟦β⟧ : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x₁)
  apply End.ext
  change Groupoid.inv c ≫ (a.asHom ≫ c) = b.asHom
  rw [← hn]
  simp

end Topology
