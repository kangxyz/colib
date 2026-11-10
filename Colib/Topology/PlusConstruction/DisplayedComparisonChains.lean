/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.PlusConstruction.DisplayedComparisonFundamentalGroup
public import Colib.Topology.LocalCoefficients.MapCancellation

/-!
# Original local-coefficient chains of a displayed plus comparison

The original comparison and its homotopy under the source are supplied. The two
plus certificates imply that this same comparison preserves every target local
system. No comparison existence, inverse, covering space or CW uniqueness is
asserted here. The companion fundamental-group theorem retains the actual track.
-/

@[expose] public section
noncomputable section
open CategoryTheory FundamentalGroupoid
universe u

namespace Topology.IsPlusConstruction
variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The supplied comparison preserves every original target local system,
by actual homotopy-factorization cancellation of the two given plus maps. -/
theorem displayedComparison_twisted_quasiIso
    (f : C(X, Y)) (g : C(X, Z)) (k : C(Y, Z)) (H : (k.comp f).Homotopy g)
    {x : X} {y : Y} {z : Z} (γ : Path (f x) y) (δ : Path (g x) z)
    (N : Subgroup (HomotopyGroup.Pi 1 X x))
    (hf : IsPlusConstruction.{u, u, u} f γ N)
    (hg : IsPlusConstruction.{u, u, u} g δ N)
    (A : LocalCoefficients.System.{u, u} Z) :
    QuasiIso (LocalCoefficients.UniverseLift.chainMap.{u, u, u} k A) :=
  LocalCoefficients.universeLift_quasiIso_of_displayed_factorization f g k H A
    (hf.localCoefficients (LocalCoefficients.pullback k A)) (hg.localCoefficients A)


attribute [colib_ref "quillen"
  "Quillen/Topology/PlusConstruction/DisplayedComparisonRecognition.lean:37-46"
  "adaptation" "Given comparison and all original target systems in common universe u"]
  displayedComparison_twisted_quasiIso

attribute [colib_tag "COL-0515"] displayedComparison_twisted_quasiIso

end Topology.IsPlusConstruction
