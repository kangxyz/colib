/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.RelativeHomotopySquarePasting
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels

/-! Cancel a common outer track when the original source square has a constant cylinder. -/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/RelativeHomotopyStrictSquarePasting.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps and independent parameters
are retained using native Colib and Mathlib objects. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.Homotopy.RelHomotopy
variable {E F : LoopPrespectrum.{u}} {o c d e f m : E ⟶ F}

/-- The constant-source specialization of actual two-square pasting, retaining all tracks. -/
def pasteStrictSourceSquares {T : Homotopy o m}
    {Lp : Homotopy o c} {Pp : Homotopy c d} {Kp : Homotopy m d}
    {Lm : Homotopy o e} {Pm : Homotopy e f} {Km : Homotopy m f}
    (Jp : (Lp.trans Pp).RelHomotopy (T.trans Kp))
    (Jm : (Lm.trans Pm).RelHomotopy (T.trans Km)) :
    (Homotopy.refl o).RelHomotopy
      ((Lp.trans (Pp.trans ((Kp.symm.trans Km).trans Pm.symm))).trans Lm.symm) := by
  let insert {a b : E ⟶ F} (H : Homotopy a b) :
      H.RelHomotopy ((Homotopy.refl a).symm.trans H) :=
    ((reflTrans H).symm).ofLevels H ((Homotopy.refl a).symm.trans H) (fun _ => rfl)
      (fun n => Homotopy.trans_level_congr _ _ _ _ n rfl rfl)
  have J := pasteTwoSquares (Jp.trans (insert (T.trans Kp)))
    (Jm.trans (insert (T.trans Km)))
  apply J.ofLevels
  · intro n
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    change (Homotopy.refl o).level n (s, x) =
      (((Homotopy.refl o).symm.levelHomotopy n).trans
        ((Homotopy.refl o).levelHomotopy n)) (s, x)
    rw [ContinuousMap.HomotopyRel.trans_apply]
    split <;> rfl
  · intro n
    rfl

end Topology.LoopPrespectrum.Homotopy.RelHomotopy

attribute [colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RelativeHomotopyStrictSquarePasting.lean:20-43"
  "adaptation" "Actual chart cancellation for a constant strict-source cylinder"]
  Topology.LoopPrespectrum.Homotopy.RelHomotopy.pasteStrictSourceSquares
