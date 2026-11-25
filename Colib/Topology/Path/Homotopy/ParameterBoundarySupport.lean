/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.Topology.Path.Homotopy.ParameterPastingSupport
public import Colib.Topology.Path.Homotopy.BoundaryOfComparison
public import Colib.KTheory.Waldhausen.Iterated.ScalarChartPause

/-! Support of the unchanged chart-boundary, pause, collapse, and projection-pasting words.
Adapted from `ParameterBoundarySupport.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Convexity CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Path.Homotopy.ParameterSupport
variable {X : Type u} [TopologicalSpace X] {U : Set X} {a b c d : X}

/-- The original coefficient boundary construction retains only its supplied surface values. -/
theorem boundaryOfComparison_in {B : Path a b} {K : Path b c}
    {H : Path a d} {A : Path d c} {J : K.Homotopy ((B.symm.trans H).trans A)}
    (hJ : HomotopyIn U J) : HomotopyIn U (Path.Homotopy.boundaryOfComparison J) := by
  have hB : PathIn U B := by
    simpa only [Path.symm_symm] using
      path_symm (path_trans_left (path_trans_left (hom_target hJ)))
  have hH := path_trans_right (path_trans_left (hom_target hJ))
  have hA := path_trans_right (hom_target hJ)
  have route := hom_trans (hom_hcomp (hom_refl hB) hJ)
    (hom_trans (hom_symm (hom_transAssoc hB (path_trans (path_symm hB) hH) hA))
    (hom_trans (hom_hcomp (hom_symm (hom_transAssoc hB (path_symm hB) hH)) (hom_refl hA))
    (hom_trans (hom_hcomp (hom_hcomp (hom_symm (hom_reflTransSymm hB)) (hom_refl hH))
      (hom_refl hA)) (hom_hcomp (hom_reflTrans hH) (hom_refl hA)))))
  exact hom_trans (hom_symm (hom_transRefl hH))
    (hom_trans (hom_hcomp (hom_refl hH) (hom_reflTransSymm hA))
    (hom_trans (hom_symm (hom_transAssoc hH hA (path_symm hA)))
      (hom_hcomp (hom_symm route) (hom_refl (path_symm hA)))))

variable {o a₀ b₀ c₀ d₀ e₀ f₀ m : X}
/-- Both whole original projection boundaries suffice for every point of their actual pasting. -/
theorem pasteProjectionSquares_in {Dp : Path o a₀} {Dm : Path o b₀} {T : Path o m}
    {Lp : Path a₀ c₀} {Pp : Path c₀ d₀} {Kp : Path m d₀}
    {Lm : Path b₀ e₀} {Pm : Path e₀ f₀} {Km : Path m f₀}
    {Jp : (Lp.trans Pp).Homotopy (Dp.symm.trans (T.trans Kp))}
    {Jm : (Lm.trans Pm).Homotopy (Dm.symm.trans (T.trans Km))}
    (hp : HomotopyIn U Jp) (hm : HomotopyIn U Jm) :
    HomotopyIn U (Path.Homotopy.pasteProjectionSquares Jp Jm) := by
  have hDp : PathIn U Dp := by
    simpa only [Path.symm_symm] using path_symm (path_trans_left (hom_target hp))
  have hDm : PathIn U Dm := by
    simpa only [Path.symm_symm] using path_symm (path_trans_left (hom_target hm))
  have hT := path_trans_left (path_trans_right (hom_target hp))
  have hKp := path_trans_right (path_trans_right (hom_target hp))
  have hKm := path_trans_right (path_trans_right (hom_target hm))
  have hLp := path_trans_left (hom_source hp)
  have hPp := path_trans_right (hom_source hp)
  have hLm := path_trans_left (hom_source hm)
  have hPm := path_trans_right (hom_source hm)
  have first := rotate_in (projectionStraighten_in hp)
  have second : HomotopyIn U
      (show (T.symm.trans Dm).Homotopy (Km.trans (Pm.symm.trans Lm.symm)) from by
        simpa only [Path.trans_symm, Path.symm_symm] using
          (Path.Homotopy.rotate (Path.Homotopy.projectionStraighten Jm)).symm₂) := by
    intro t
    have ep : (Dm.symm.trans T).symm = T.symm.trans Dm := by
      simp only [Path.trans_symm, Path.symm_symm]
    have eq : ((Lm.trans Pm).trans Km.symm).symm = Km.trans (Pm.symm.trans Lm.symm) := by
      simp only [Path.trans_symm, Path.symm_symm]
    simp only [eq_mp_eq_cast, hom_type_cast_apply ep eq]
    exact hom_symm₂ (rotate_in (projectionStraighten_in hm)) t
  have insert0 := hom_hcomp (hom_refl (path_symm hDp)) (hom_symm (hom_reflTrans hDm))
  have insert1 := hom_hcomp (hom_refl (path_symm hDp))
    (hom_hcomp (hom_reflTransSymm hT) (hom_refl hDm))
  have insert2 := hom_hcomp (hom_refl (path_symm hDp)) (hom_transAssoc hT (path_symm hT) hDm)
  have insert3 := hom_symm (hom_transAssoc (path_symm hDp) hT (path_trans (path_symm hT) hDm))
  have ins := hom_trans insert0 (hom_trans insert1 (hom_trans insert2 insert3))
  have tail1 := hom_transAssoc (path_trans hLp hPp) (path_symm hKp)
    (path_trans hKm (path_trans (path_symm hPm) (path_symm hLm)))
  have tail2 := hom_hcomp (hom_refl (path_trans hLp hPp))
    (hom_symm (hom_transAssoc (path_symm hKp) hKm (path_trans (path_symm hPm) (path_symm hLm))))
  have tail3 := hom_hcomp (hom_refl (path_trans hLp hPp))
    (hom_symm (hom_transAssoc (path_trans (path_symm hKp) hKm) (path_symm hPm) (path_symm hLm)))
  have tail4 := hom_symm (hom_transAssoc (path_trans hLp hPp)
    (path_trans (path_trans (path_symm hKp) hKm) (path_symm hPm)) (path_symm hLm))
  have tail5 := hom_hcomp
    (hom_transAssoc hLp hPp (path_trans (path_trans (path_symm hKp) hKm) (path_symm hPm)))
    (hom_refl (path_symm hLm))
  exact hom_trans (hom_trans ins (hom_hcomp first second))
    (hom_trans tail1 (hom_trans tail2 (hom_trans tail3 (hom_trans tail4 tail5))))

section Simplex
variable {k : ℕ} {U : Set (StdSimplex ℝ (Fin (k + 1)))}
variable {a₀ b₀ a₁ b₁ : StdSimplex ℝ (Fin (k + 1))}
variable {p : Path a₀ b₀} {l : Path a₀ a₁} {q : Path a₁ b₁} {m : Path b₀ b₁}

/-- The native terminal pause never leaves the original boundary's range. -/
theorem pauseRight_in {J : p.Homotopy ((l.trans q).trans m.symm)}
    (hJ : HomotopyIn U J) : HomotopyIn U (pauseRightParameter J) := by
  have hlq := path_trans_left (hom_target hJ)
  have hm : PathIn U m := by
    simpa only [Path.symm_symm] using path_symm (path_trans_right (hom_target hJ))
  exact hom_trans hJ (hom_hcomp (hom_refl hlq) (hom_symm₂ (hom_symm (hom_transRefl hm))))

/-- Surjectivity of the actual collapse retains every original scalar value in its support. -/
theorem collapsed_in {J : p.Homotopy ((l.trans q).trans m.symm)}
    (hJ : HomotopyIn U J) (t : unitInterval × unitInterval) : collapsed J t ∈ U := by
  obtain ⟨s, hs⟩ := Topology.ThreeSideSquare.collapse_surjective t
  rw [← hs, collapsed_collapse]
  exact hJ s
end Simplex
end Path.Homotopy.ParameterSupport
