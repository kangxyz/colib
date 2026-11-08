/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Colib.Util.References

/-! The literal scalar path word underlying the native three-route pasting. -/
/-! Implementation provenance: `Quillen/Topology/Path/HomotopyThreeRoutes.lean:19-55`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Literal path words are retained. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u
namespace Path.Homotopy
variable {X : Type u} [TopologicalSpace X]
variable {a b c d : X}

/-- Scalar counterpart of the native two-route rotation. -/
def rotate {H : Path a b} {K : Path b d} {L : Path a c}
    {M : Path c d} (J : (H.trans K).Homotopy (L.trans M)) :
    (H.symm.trans L).Homotopy (K.trans M.symm) := by
  have j1 := (refl H.symm).hcomp (transRefl L).symm
  have j2 := (refl H.symm).hcomp ((refl L).hcomp (reflTransSymm M))
  have j3 := (refl H.symm).hcomp (transAssoc L M M.symm).symm
  have j4 := (refl H.symm).hcomp (J.symm.hcomp (refl M.symm))
  have j5 := (transAssoc H.symm (H.trans K) M.symm).symm
  have j6 := ((transAssoc H.symm H K).symm).hcomp (refl M.symm)
  have j7 := ((reflSymmTrans H).symm.hcomp (refl K)).hcomp (refl M.symm)
  have j8 := (reflTrans K).hcomp (refl M.symm)
  exact j1.trans (j2.trans (j3.trans (j4.trans (j5.trans (j6.trans (j7.trans j8))))))

variable {o a₀ b₀ c₀ d₀ e₀ f₀ z : X}
/-- The exact three-route word of the native rectangle, at scalar level. -/
def threeRoutes {C : Path o a₀} {D : Path a₀ b₀} {E' : Path o c₀}
    {F' : Path c₀ b₀} {G : Path o d₀} {H : Path d₀ e₀} {Ipath : Path c₀ e₀}
    {J : Path o f₀} {K : Path f₀ z} {L : Path d₀ z}
    (j1 : (C.trans D).Homotopy (E'.trans F'))
    (j2 : (G.trans H).Homotopy (E'.trans Ipath))
    (j3 : (G.trans L).Homotopy (J.trans K)) :
    ((F'.symm.trans Ipath).trans (H.symm.trans L)).Homotopy
      (D.symm.trans ((C.symm.trans J).trans K)) := by
  have rotateMiddle : (Ipath.trans H.symm).Homotopy (E'.symm.trans G) := by
    simpa only [Path.trans_symm, Path.symm_symm] using (rotate j2).symm₂.symm
  have reverseFirst : (F'.symm.trans E'.symm).Homotopy (D.symm.trans C.symm) := by
    simpa only [Path.trans_symm] using j1.symm₂.symm
  exact ((transAssoc (F'.symm.trans Ipath) H.symm L).symm.trans
    ((transAssoc F'.symm Ipath H.symm).hcomp (refl L))).trans
    (((refl F'.symm).hcomp rotateMiddle).hcomp (refl L) |>.trans
      (((transAssoc F'.symm E'.symm G).symm.hcomp (refl L)).trans
        ((transAssoc (F'.symm.trans E'.symm) G L).trans
          ((reverseFirst.hcomp j3).trans
            ((transAssoc D.symm C.symm (J.trans K)).trans
              ((refl D.symm).hcomp (transAssoc C.symm J K).symm))))))
end Path.Homotopy

attribute [colib_ref "quillen"
    "Quillen/Topology/Path/HomotopyThreeRoutes.lean:19-55" "adaptation"
    "The actual rotated and three-route path concatenations"]
  Path.Homotopy.rotate Path.Homotopy.threeRoutes
