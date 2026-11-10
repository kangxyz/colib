/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.UniverseLift
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportGroup
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Homological certification of an original plus-construction map

`IsPlusConstruction` records the local-coefficient characterization in the
explicit coefficient universe: the actual based fundamental-group map is
surjective with the specified perfect kernel, and the original continuous map
preserves homology for every target local system. The source and target are
path-connected. The chosen basepoint path is retained in the induced map.

For connected CW spaces, when the coefficient universe is large enough, this
is the usual homological characterization of a plus construction (Weibel,
*The K-book*, IV.1.4.1 and IV.1.6). This module uses that characterization as
its definition. It does not prove a general CW
existence theorem, uniqueness, or equivalence with homotopy-fiber acyclicity.
In particular, construction of a value of this predicate must discharge every
local-coefficient comparison; naming the predicate supplies no such proof.
-/

@[expose] public section
noncomputable section
open CategoryTheory
universe u v w
namespace Topology
open FundamentalGroupoid
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual fundamental-group map, corrected by the specified basepoint path. -/
def basedPiOneMap (f : C(X, Y)) {x : X} {y : Y} (γ : Path (f x) y) :
    HomotopyGroup.Pi 1 X x →* HomotopyGroup.Pi 1 Y y :=
  (pathTransportMulEquiv γ 0).toMonoidHom.comp (HomotopyGroup.piMap 0 f rfl)

/-- Homological plus-construction certification in coefficient universe `w`.
All fields refer to the specified original map, path, subgroup, and actual chains. -/
structure IsPlusConstruction (f : C(X, Y)) {x : X} {y : Y} (γ : Path (f x) y)
    (N : Subgroup (HomotopyGroup.Pi 1 X x)) : Prop where
  /-- The actual source is path-connected. -/
  sourcePathConnected : PathConnectedSpace X
  /-- The actual target is path-connected. -/
  targetPathConnected : PathConnectedSpace Y
  /-- The specified subgroup is perfect. -/
  perfect : Group.IsPerfect N
  /-- The original based map is surjective on the fundamental group. -/
  surjective : Function.Surjective (basedPiOneMap f γ)
  /-- The specified subgroup is precisely the kernel of the original based map. -/
  kernelEq : (basedPiOneMap f γ).ker = N
  /-- Every target system in the stated universe is preserved by the original chain map. -/
  localCoefficients : ∀ A : LocalCoefficients.System.{v, w} Y,
    QuasiIso (LocalCoefficients.UniverseLift.chainMap f A)

namespace IsPlusConstruction
variable {f : C(X, Y)} {x : X} {y : Y} {γ : Path (f x) y}
  {N : Subgroup (HomotopyGroup.Pi 1 X x)} (h : IsPlusConstruction.{u, v, w} f γ N)

include h in
/-- Normality follows from the proved equality with the original kernel. -/
theorem normal : N.Normal := by
  rw [← h.kernelEq]
  infer_instance

include h in
/-- The certificate retains the original map in every local homology degree. -/
theorem homologyMap_isIso (A : LocalCoefficients.System.{v, w} Y) (n : ℕ) :
    IsIso (LocalCoefficients.UniverseLift.homologyMap f A n) := by
  have := h.localCoefficients A
  change IsIso (HomologicalComplex.homologyMap
    (LocalCoefficients.UniverseLift.chainMap f A) n)
  infer_instance

end IsPlusConstruction

attribute [colib_ref "quillen"
  "Quillen/Topology/PlusConstruction/Basic.lean:38-41"
  "adaptation" "Original specified based map and arbitrary target local-coefficient chains"]
  basedPiOneMap

attribute [colib_ref "quillen"
  "Quillen/Topology/PlusConstruction/Basic.lean:43-59"
  "adaptation" "Original specified based map and arbitrary target local-coefficient chains"]
  IsPlusConstruction

attribute [colib_ref "quillen"
  "Quillen/Topology/PlusConstruction/Basic.lean:65-69"
  "adaptation" "Original specified based map and arbitrary target local-coefficient chains"]
  IsPlusConstruction.normal

attribute [colib_ref "quillen"
  "Quillen/Topology/PlusConstruction/Basic.lean:71-78"
  "adaptation" "Original specified based map and arbitrary target local-coefficient chains"]
  IsPlusConstruction.homologyMap_isIso

end Topology
