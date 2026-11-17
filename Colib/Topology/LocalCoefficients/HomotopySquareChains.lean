/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.LocalCoefficients.HomotopySquare
public import Colib.Topology.LocalCoefficients.HomotopyQuasiIso

/-!
# Original twisted chain maps across a square of genuine homotopy equivalences

The vertical equivalences point toward the original map. Their inverse
homotopies construct the opposite square; the target system is pulled back
along the actual inverse map. No target system is identified with a retraction
pullback without its genuine coefficient transport.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u

namespace FundamentalGroupoid.LocalCoefficients
variable {X Y X' Y' : Type u}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']

/-- A strict square with genuine vertical equivalences transfers all original
target-system chain quasi-isomorphisms to the original opposite map. -/
theorem pushforwardChainMap_quasiIso_of_equivalence_square
    (s : ContinuousMap.HomotopyEquiv X' X) (p : ContinuousMap.HomotopyEquiv Y' Y)
    (f : C(X, Y)) (g : C(X', Y')) (w : p.toFun.comp g = f.comp s.toFun)
    (hf : ∀ A : System.{u, u} Y, QuasiIso (pushforwardChainMap f A))
    (A : System.{u, u} Y') : QuasiIso (pushforwardChainMap g A) := by
  let H₀ := (p.left_inv.some.compContinuousMap (g.comp s.invFun)).symm
  let H₁ := (ContinuousMap.Homotopy.refl (p.invFun.comp f)).comp s.right_inv.some
  have hw : (p.invFun.comp p.toFun).comp (g.comp s.invFun) =
      (p.invFun.comp f).comp (s.toFun.comp s.invFun) := by
    ext x
    exact congrArg p.invFun (ContinuousMap.congr_fun w (s.invFun x))
  let H : (g.comp s.invFun).Homotopy (p.invFun.comp f) :=
    (H₀.cast rfl hw).trans (H₁.cast rfl rfl)
  let := hf (pullback p.invFun A)
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  change IsIso (pushforwardHomologyMap g A n)
  apply isIso_pushforwardHomologyMap_of_homotopySquare s.symm p.symm f g H A n
  change IsIso (HomologicalComplex.homologyMap (pushforwardChainMap f (pullback p.invFun A)) n)
  infer_instance

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/HomotopySquareChains.lean:33-53"
  "adaptation" "Exact homotopy-square transfer with actual coefficient pullback"]
  pushforwardChainMap_quasiIso_of_equivalence_square

end FundamentalGroupoid.LocalCoefficients
