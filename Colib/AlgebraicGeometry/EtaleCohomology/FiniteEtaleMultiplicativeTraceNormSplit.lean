/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleMultiplicativeTraceUnits
public import Colib.AlgebraicGeometry.EtaleCohomology.SplitAffinePullback
public import Colib.RingTheory.Norm.SplitProduct

/-! # Native multiplicative trace versus norm on an affine split chart -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct
universe u
namespace Stacks.EtaleCohomology
open AlgebraicGeometry.SplitAffinePullback
variable {k R A : Type u} [CommRing k] [CommRing R] [CommRing A]
  [Algebra k R] [Algebra k A] [Module.Free k A] [Module.Finite k A]
  {I : Type u} [Finite I]
  [Etale (baseMap (k := k) (R := R))]
  [Etale (sourceMap (k := k) (A := A))] [IsFinite (sourceMap (k := k) (A := A))]
variable (e : pullback (baseMap (k := k) (R := R)) (sourceMap (k := k) (A := A)) ≅
  ∐ fun _ : I => Spec (.of R))
  (he : e.hom ≫ Sigma.desc (fun _ : I => 𝟙 (Spec (.of R))) =
    pullback.fst (baseMap (k := k) (R := R)) (sourceMap (k := k) (A := A)))

/-- Actual sheet data supplied by the actual affine splitting over the base. -/
def affineSplitSheetData : Stacks.Etale.IsSplitOver
    (sourceMap (k := k) (A := A)) (baseMap (k := k) (R := R)) :=
  Stacks.Etale.isSplitOverOfIso _ _
    (pullbackSymmetry _ _ ≪≫ e) (by simp [he])

set_option backward.isDefEq.respectTransparency false in
include e he in
/-- The native trace evaluated on an affine split chart is the base-changed determinant norm. -/
theorem finiteEtaleMultiplicativeTraceUnits_affineSplit (t : Aˣ) :
    (Scheme.ΓSpecIso (.of R)).hom.hom
      (finiteEtaleMultiplicativeTraceUnits (sourceMap (k := k) (A := A))
        (Scheme.Etale.mk (baseMap (k := k) (R := R)))
        (Units.map (Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom t)).val =
      algebraMap k R (Algebra.norm k t.val) := by
  let : Fintype I := Fintype.ofFinite I
  rw [finiteEtaleMultiplicativeTraceUnits_split _ _ (affineSplitSheetData e he)]
  rw [Algebra.map_norm_eq_split_product (splitAlgEquiv e he)]
  simp only [Units.coe_prod]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [splitAlgEquiv_component]
  congr 2
  change (Sigma.ι (fun _ : I => Spec (.of R)) i ≫
    (pullbackSymmetry _ _ ≪≫ e).inv ≫ pullback.fst _ _).appTop.hom _ = _
  simp [Iso.trans_inv, Category.assoc, splitSheet]

end Stacks.EtaleCohomology
