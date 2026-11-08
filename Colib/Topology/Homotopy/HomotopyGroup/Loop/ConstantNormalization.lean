/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.KOneNormalization

/-!
# Normalization at the constant loop

The specified left component translation is the identity on homotopy classes
at the constant loop, via the actual unit homotopy and its displayed boundary.
-/
/-! Implementation provenance:
`Quillen/Topology/HomotopyGroups/Loop/ConstantNormalization.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u
namespace Topology
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Constant left translation and its prescribed correction act identically on classes. -/
@[colib_ref "quillen"
    "Topology/HomotopyGroups/Loop/ConstantNormalization.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem loopLeftComponentHomotopyEquiv_refl (n : ℕ)
    (a : HomotopyGroup.Pi n (Path x x) (Path.refl x)) :
    loopLeftComponentHomotopyEquiv (Path.refl x) n a = a := by
  induction a using Quotient.inductionOn with
  | h p =>
    change pathTransport (loopRightUnitPath (Path.refl x)) n
      (Quotient.mk' (GenLoop.postcomp (loopLeftTranslationEquiv (Path.refl x)).toFun _ p)) =
        Quotient.mk' p
    apply pathTransport_eq_of_cube_homotopy (loopRightUnitPath (Path.refl x)) n
      (GenLoop.postcomp (loopLeftTranslationEquiv (Path.refl x)).toFun _ p) p
      { toFun z := Path.delayReflLeft z.1 (p z.2)
        continuous_toFun := Path.continuous_delayReflLeft.comp
          (continuous_fst.prodMk (p.val.continuous.comp continuous_snd))
        map_zero_left := fun s ↦ by
          change Path.delayReflLeft 0 (p s) = loopLeftTranslationEquiv (Path.refl x) (p s)
          rw [Path.delayReflLeft_zero, loopLeftTranslationEquiv_apply]
        map_one_left := fun s ↦ Path.delayReflLeft_one (p s) }
    intro t s hs
    change Path.delayReflLeft t (p s) = loopRightUnitPath (Path.refl x) t
    exact (congrArg (Path.delayReflLeft t) (p.property s hs)).trans (by
      ext r
      rfl)

/-- At the constant component the original normalization is the ordinary loop degree shift. -/
@[colib_ref "quillen"
    "Topology/HomotopyGroups/Loop/ConstantNormalization.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem loopKOneNormalization_refl (a : FundamentalGroup (Path x x) (Path.refl x)) :
    loopKOneNormalization (Path.refl x) a =
      (loopShiftMulEquiv 0).symm (HomotopyGroup.pi1MulEquivFundamentalGroup.symm a) := by
  rw [loopKOneNormalization_eq]
  congr 1
  apply (loopLeftComponentHomotopyEquiv (Path.refl x) 1).injective
  rw [Equiv.apply_symm_apply, loopLeftComponentHomotopyEquiv_refl]

end Topology
