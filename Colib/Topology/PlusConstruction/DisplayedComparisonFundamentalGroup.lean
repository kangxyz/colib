/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.GroupTheory.MonoidHom.KernelComparison
public import Colib.Topology.PlusConstruction.Basic
public import Colib.Topology.Homotopy.HomotopyGroup.MovingBasepoint
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportComposition
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportHomotopy

/-!
# Fundamental groups of a displayed comparison between plus maps

A continuous comparison map and an actual homotopy under the original source
are explicit inputs. Equal original kernels and surjective original maps then
force its Pi one map to be bijective. No comparison map is constructed here.
The coherent target-basepoint path retains the actual homotopy track and works
for nonabelian groups, without arbitrary-path cancellation.
-/

@[expose] public section
noncomputable section
universe u v t w

namespace Topology
variable {X : Type u} {Y : Type v} {Z : Type t}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Basepoint transport changes no element of the kernel of the original map. -/
theorem basedPiOneMap_ker (f : C(X, Y)) {x : X} {y : Y} (γ : Path (f x) y) :
    (basedPiOneMap f γ).ker = (HomotopyGroup.piMap 0 f (x := x) rfl).ker := by
  ext a
  change pathTransportMulEquiv γ 0 (HomotopyGroup.piMap 0 f rfl a) = 1 ↔
    HomotopyGroup.piMap 0 f rfl a = 1
  constructor
  · intro ha
    apply (pathTransportMulEquiv γ 0).injective
    simpa only [map_one] using ha
  · intro ha
    rw [ha, map_one]

/-- Surjectivity is unchanged by the specified target-basepoint transport. -/
theorem basedPiOneMap_surjective_iff (f : C(X, Y)) {x : X} {y : Y}
    (γ : Path (f x) y) :
    Function.Surjective (basedPiOneMap f γ) ↔
      Function.Surjective (HomotopyGroup.piMap 0 f (x := x) rfl) := by
  constructor
  · intro hf a
    obtain ⟨b, hb⟩ := hf (pathTransportMulEquiv γ 0 a)
    exact ⟨b, (pathTransportMulEquiv γ 0).injective hb⟩
  · intro hf a
    obtain ⟨b, hb⟩ := hf ((pathTransportMulEquiv γ 0).symm a)
    exact ⟨b, (congrArg (pathTransportMulEquiv γ 0) hb).trans
      ((pathTransportMulEquiv γ 0).apply_symm_apply a)⟩

/-- Bijectivity is unchanged by that same actual basepoint transport. -/
theorem basedPiOneMap_bijective_iff (f : C(X, Y)) {x : X} {y : Y}
    (γ : Path (f x) y) :
    Function.Bijective (basedPiOneMap f γ) ↔
      Function.Bijective (HomotopyGroup.piMap 0 f (x := x) rfl) := by
  constructor
  · intro hf
    exact ⟨fun a b hab ↦ hf.injective (congrArg (pathTransportMulEquiv γ 0) hab),
      (basedPiOneMap_surjective_iff f γ).mp hf.surjective⟩
  · intro hf
    exact ⟨fun a b hab ↦ hf.injective ((pathTransportMulEquiv γ 0).injective hab),
      (basedPiOneMap_surjective_iff f γ).mpr hf.surjective⟩

/-- The basepoint path for a displayed under-source comparison uses its exact
homotopy track; arbitrary target loops are not silently discarded. -/
def displayedComparisonPath (f : C(X, Y)) (g : C(X, Z)) (k : C(Y, Z))
    (H : (k.comp f).Homotopy g) {x : X} {y : Y} {z : Z}
    (γ : Path (f x) y) (δ : Path (g x) z) : Path (k y) z :=
  (γ.map k.continuous).symm.trans ((H.evalAt x).trans δ)

/-- The original corrected fundamental-group maps commute for this coherent
path, including nonabelian target groups. -/
theorem basedPiOneMap_displayedComparison (f : C(X, Y)) (g : C(X, Z)) (k : C(Y, Z))
    (H : (k.comp f).Homotopy g) {x : X} {y : Y} {z : Z}
    (γ : Path (f x) y) (δ : Path (g x) z) :
    (basedPiOneMap k (displayedComparisonPath f g k H γ δ)).comp (basedPiOneMap f γ) =
      basedPiOneMap g δ := by
  ext a
  change pathTransport (displayedComparisonPath f g k H γ δ) 1
      (HomotopyGroup.map k rfl (pathTransport γ 1 (HomotopyGroup.map f rfl a))) =
    pathTransport δ 1 (HomotopyGroup.map g rfl a)
  rw [← pathTransport_naturality, displayedComparisonPath,
    pathTransport_trans, pathTransport_trans, pathTransport_symm_apply,
    ← HomotopyGroup.map_comp]
  exact congrArg (pathTransport δ 1) (pathTransport_homotopyGroupMap_homotopy H x 1 a)

/-- A supplied comparison and supplied under-source homotopy between two plus
maps with the same subgroup force its original Pi one map to be bijective.
This theorem does not construct either the comparison or its homotopy. -/
theorem IsPlusConstruction.displayedComparison_piOne_bijective
    (f : C(X, Y)) (g : C(X, Z)) (k : C(Y, Z)) (H : (k.comp f).Homotopy g)
    {x : X} {y : Y} {z : Z} (γ : Path (f x) y) (δ : Path (g x) z)
    (N : Subgroup (HomotopyGroup.Pi 1 X x))
    (hf : IsPlusConstruction.{u, v, w} f γ N)
    (hg : IsPlusConstruction.{u, t, w} g δ N) :
    Function.Bijective (HomotopyGroup.piMap 0 k (x := y) rfl) := by
  apply (basedPiOneMap_bijective_iff k (displayedComparisonPath f g k H γ δ)).mp
  exact MonoidHom.bijective_of_surjective_equal_kernels
    (basedPiOneMap f γ) (basedPiOneMap g δ)
    (basedPiOneMap k (displayedComparisonPath f g k H γ δ))
    hf.surjective hg.surjective (hf.kernelEq.trans hg.kernelEq.symm)
    (basedPiOneMap_displayedComparison f g k H γ δ)


attribute [colib_ref "quillen"
  "Quillen/Topology/PlusConstruction/DisplayedComparisonFundamentalGroup.lean:36-45"
  "adaptation" "Actual comparison and original homotopy track with nonabelian fundamental groups"]
  basedPiOneMap_ker

attribute [colib_ref "quillen"
  "Quillen/Topology/PlusConstruction/DisplayedComparisonFundamentalGroup.lean:48-59"
  "adaptation" "Actual comparison and original homotopy track with nonabelian fundamental groups"]
  basedPiOneMap_surjective_iff

attribute [colib_ref "quillen"
  "Quillen/Topology/PlusConstruction/DisplayedComparisonFundamentalGroup.lean:62-72"
  "adaptation" "Actual comparison and original homotopy track with nonabelian fundamental groups"]
  basedPiOneMap_bijective_iff

attribute [colib_ref "quillen"
  "Quillen/Topology/PlusConstruction/DisplayedComparisonFundamentalGroup.lean:76-79"
  "adaptation" "Actual comparison and original homotopy track with nonabelian fundamental groups"]
  displayedComparisonPath

attribute [colib_ref "quillen"
  "Quillen/Topology/PlusConstruction/DisplayedComparisonFundamentalGroup.lean:83-95"
  "adaptation" "Actual comparison and original homotopy track with nonabelian fundamental groups"]
  basedPiOneMap_displayedComparison

attribute [colib_ref "quillen"
  "Quillen/Topology/PlusConstruction/DisplayedComparisonFundamentalGroup.lean:100-112"
  "adaptation" "Actual comparison and original homotopy track with nonabelian fundamental groups"]
  IsPlusConstruction.displayedComparison_piOne_bijective

attribute [colib_tag "COL-0515"] IsPlusConstruction.displayedComparison_piOne_bijective

end Topology
