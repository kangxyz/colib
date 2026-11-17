/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.LocalCoefficients.UniverseLift
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Exact same-universe quasi-isomorphism comparison for the original lifted chains -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u

namespace FundamentalGroupoid.LocalCoefficients.UniverseLift
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The original UniverseLift and same-universe spatial chain maps are
quasi-isomorphisms simultaneously. This performs no change of universe. -/
theorem quasiIso_chainMap_iff (f : C(X, Y)) (A : System.{u, u} Y) :
    QuasiIso (chainMap.{u, u, u} f A) ↔ QuasiIso (pushforwardChainMap f A) := by
  rw [quasiIso_iff, quasiIso_iff]
  apply forall_congr'
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_homologyMap_iff f A n

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/UniverseLiftQuasiIso.lean:22-28"
  "adaptation" "The actual chains in a single coefficient and space universe"]
  quasiIso_chainMap_iff

end FundamentalGroupoid.LocalCoefficients.UniverseLift
