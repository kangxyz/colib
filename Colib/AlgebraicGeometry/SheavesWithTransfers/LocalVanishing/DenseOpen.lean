/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.IntegralAffine
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Basic
public import Colib.AlgebraicGeometry.Sites.Smooth.SectionDetection

/-!
# Dense-open detection for Nisnevich sheaves with transfers

Adapted from `Motivic/Cohomology/A1/LocalVanishing/Coefficient.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `3b918a1a2a6881bfa0fbf84e0bbccfeb63e1b1d3`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme PresheafWithTransfers

variable {k : Type u} [Field k]

/-- Separatedness is used only for the original Nisnevich sheaf coefficient. -/
theorem section_eq_zero_of_dense_open_of_integralAffineLocalZero
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k) {X A : SmoothSite (Spec (.of k))}
    (a : A ⟶ X) [IsOpenImmersion a.left] (ha : DenseRange a.left)
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (s : F.obj.sections (Cor.mk X))
    (hs : F.obj.transfer ((Cor.graphFunctor k).map a) s = 0) : s = 0 := by
  classical
  have hlocal := exists_zero_neighborhood_of_dense_open_of_integralAffineLocalZero
    hD a ha F.obj hF s hs
  choose O hO hx hz using hlocal
  exact SmoothSite.section_eq_zero_of_residue_splitting_family
    ((SheafWithTransfers.toSheaf k).obj F)
    (fun x => SmoothSite.mk ((O x).ι ≫ X.hom))
    (fun x => SmoothSite.homMk (O x).ι rfl)
    (fun x => inferInstanceAs (Etale (O x).ι))
    (fun x => ⟨x, ⟨x, hx x⟩, rfl,
      inferInstanceAs (IsIso ((O x).ι.residueFieldMap ⟨x, hx x⟩))⟩) s hz

end AlgebraicGeometry.SheafWithTransfers
