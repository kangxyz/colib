/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.Topology.Path.Homotopy.ParameterRangeClosure

/-! The original scalar pasting words stay in the union of their constituent ranges.
Adapted from `ParameterPastingSupport.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u
namespace Path.Homotopy.ParameterSupport
variable {X : Type u} [TopologicalSpace X] {U : Set X} {a b c d : X}

/-- The literal eight-stage rotation introduces no new scalar value. -/
theorem rotate_in {H : Path a b} {K : Path b d} {L : Path a c} {M : Path c d}
    {J : (H.trans K).Homotopy (L.trans M)} (hJ : HomotopyIn U J) :
    HomotopyIn U (Path.Homotopy.rotate J) := by
  have hH := path_trans_left (hom_source hJ)
  have hK := path_trans_right (hom_source hJ)
  have hL := path_trans_left (hom_target hJ)
  have hM := path_trans_right (hom_target hJ)
  unfold Path.Homotopy.rotate
  exact hom_trans (hom_hcomp (hom_refl (path_symm hH)) (hom_symm (hom_transRefl hL)))
    (hom_trans (hom_hcomp (hom_refl (path_symm hH))
      (hom_hcomp (hom_refl hL) (hom_reflTransSymm hM)))
    (hom_trans (hom_hcomp (hom_refl (path_symm hH))
      (hom_symm (hom_transAssoc hL hM (path_symm hM))))
    (hom_trans (hom_hcomp (hom_refl (path_symm hH))
      (hom_hcomp (hom_symm hJ) (hom_refl (path_symm hM))))
    (hom_trans (hom_symm (hom_transAssoc (path_symm hH) (path_trans hH hK) (path_symm hM)))
    (hom_trans (hom_hcomp (hom_symm (hom_transAssoc (path_symm hH) hH hK))
      (hom_refl (path_symm hM)))
    (hom_trans (hom_hcomp (hom_hcomp (hom_symm (hom_reflSymmTrans hH)) (hom_refl hK))
      (hom_refl (path_symm hM)))
      (hom_hcomp (hom_reflTrans hK) (hom_refl (path_symm hM)))))))))

variable {o a₀ b₀ c₀ d₀ e₀ f₀ z : X}
/-- The full native three-route word stays in the three supplied comparison surfaces. -/
theorem threeRoutes_in {C : Path o a₀} {D : Path a₀ b₀} {E' : Path o c₀}
    {F' : Path c₀ b₀} {G : Path o d₀} {H : Path d₀ e₀} {Ipath : Path c₀ e₀}
    {J : Path o f₀} {K : Path f₀ z} {L : Path d₀ z}
    {j1 : (C.trans D).Homotopy (E'.trans F')}
    {j2 : (G.trans H).Homotopy (E'.trans Ipath)}
    {j3 : (G.trans L).Homotopy (J.trans K)}
    (h1 : HomotopyIn U j1) (h2 : HomotopyIn U j2) (h3 : HomotopyIn U j3) :
    HomotopyIn U (Path.Homotopy.threeRoutes j1 j2 j3) := by
  have hC := path_trans_left (hom_source h1)
  have hD := path_trans_right (hom_source h1)
  have hE := path_trans_left (hom_target h1)
  have hF := path_trans_right (hom_target h1)
  have hG := path_trans_left (hom_source h2)
  have hH := path_trans_right (hom_source h2)
  have hI := path_trans_right (hom_target h2)
  have hJ := path_trans_left (hom_target h3)
  have hK := path_trans_right (hom_target h3)
  have hL := path_trans_right (hom_source h3)
  have hrot : HomotopyIn U (show (Ipath.trans H.symm).Homotopy (E'.symm.trans G) from by
      simpa only [Path.trans_symm, Path.symm_symm] using (Path.Homotopy.rotate j2).symm₂.symm) := by
    intro t
    have ep : (H.trans Ipath.symm).symm = Ipath.trans H.symm := by
      simp only [Path.trans_symm, Path.symm_symm]
    have eq : (G.symm.trans E').symm = E'.symm.trans G := by
      simp only [Path.trans_symm, Path.symm_symm]
    simp only [eq_mp_eq_cast, hom_type_cast_apply ep eq]
    exact hom_symm (hom_symm₂ (rotate_in h2)) t
  have hrev : HomotopyIn U (show (F'.symm.trans E'.symm).Homotopy (D.symm.trans C.symm) from by
      simpa only [Path.trans_symm] using j1.symm₂.symm) := by
    intro t
    have ep : (E'.trans F').symm = F'.symm.trans E'.symm := Path.trans_symm _ _
    have eq : (C.trans D).symm = D.symm.trans C.symm := Path.trans_symm _ _
    simp only [eq_mp_eq_cast, hom_type_cast_apply ep eq]
    exact hom_symm (hom_symm₂ h1) t
  unfold Path.Homotopy.threeRoutes
  exact hom_trans
    (hom_trans (hom_symm (hom_transAssoc (path_trans (path_symm hF) hI) (path_symm hH) hL))
      (hom_hcomp (hom_transAssoc (path_symm hF) hI (path_symm hH)) (hom_refl hL)))
    (hom_trans (hom_hcomp
      (hom_hcomp (hom_refl (path_symm hF)) hrot)
      (hom_refl hL))
    (hom_trans (hom_hcomp (hom_symm (hom_transAssoc (path_symm hF) (path_symm hE) hG))
      (hom_refl hL))
    (hom_trans (hom_transAssoc (path_trans (path_symm hF) (path_symm hE)) hG hL)
    (hom_trans (hom_hcomp hrev h3)
    (hom_trans (hom_transAssoc (path_symm hD) (path_symm hC) (path_trans hJ hK))
      (hom_hcomp (hom_refl (path_symm hD))
        (hom_symm (hom_transAssoc (path_symm hC) hJ hK))))))))

/-- Initial straightening retains the range of the original supplied boundary. -/
theorem projectionStraighten_in {x y z w : X} {D : Path x y} {A : Path y w}
    {T : Path x z} {K : Path z w}
    {J : A.Homotopy (D.symm.trans (T.trans K))} (hJ : HomotopyIn U J) :
    HomotopyIn U (Path.Homotopy.projectionStraighten J) := by
  have hD : PathIn U D := by
    simpa only [Path.symm_symm] using path_symm (path_trans_left (hom_target hJ))
  have hTK := path_trans_right (hom_target hJ)
  exact hom_trans (hom_hcomp (hom_refl hD) hJ)
    (hom_trans (hom_symm (hom_transAssoc hD (path_symm hD) hTK))
      (hom_trans (hom_hcomp (hom_symm (hom_reflTransSymm hD)) (hom_refl hTK))
        (hom_reflTrans hTK)))

end Path.Homotopy.ParameterSupport
