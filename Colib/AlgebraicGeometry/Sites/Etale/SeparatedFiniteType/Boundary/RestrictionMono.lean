/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.LocalVanishing.DenseOpen
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Cokernel
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Dense restriction on the small Nisnevich site

Adapted from `Motivic/Cohomology/A1/LocalVanishing/Coefficient.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `3b918a1a2a6881bfa0fbf84e0bbccfeb63e1b1d3`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k]

/-- The literal coefficient restriction is monic, tested on actual etale objects. -/
theorem restrictionToDirectImage_mono_of_dense_of_integralAffineLocalZero
    (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
    {U Y : SmoothSite (Spec (.of k))} (j : U ⟶ Y) [IsOpenImmersion j.left]
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)
    (hj : DenseRange j.left) :
    Mono (restrictionToDirectImage ((SheafWithTransfers.toSheaf k).obj F) j) := by
  apply (sheafToPresheaf _ _).mono_of_mono_map
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro V
  apply (AddCommGrpCat.mono_iff_injective _).mpr
  apply (injective_iff_map_eq_zero _).mpr
  intro s hs
  let a := (restrictionProjection j).app V.unop
  let : IsOpenImmersion a.left :=
    inferInstanceAs (IsOpenImmersion (pullback.fst V.unop.hom j.left))
  have ha : DenseRange a.left := by
    change Dense (Set.range (pullback.fst V.unop.hom j.left))
    rw [IsOpenImmersion.range_pullbackFst]
    exact hj.preimage V.unop.hom.isOpenMap
  exact SheafWithTransfers.section_eq_zero_of_dense_open_of_integralAffineLocalZero
    hD a ha F hF s hs

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
