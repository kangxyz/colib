/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleKummerTrace

/-! # Native multiplicative trace on a split chart -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Stacks.EtaleCohomology
open Stacks.Kummer
variable {S Y : Scheme.{u}} (g : Y ⟶ S) [Etale g] [IsFinite g]

set_option backward.isDefEq.respectTransparency false in
/-- The actual native Gm trace is the product of restriction maps on a split chart. -/
theorem finiteEtaleMultiplicativeTrace_split_apply (U : S.Etale)
    (h : Stacks.Etale.IsSplitOver g U.hom)
    (t : Γ((baseChangeCompose g U).left, ⊤)ˣ) :
    letI : Finite h.I := h.finite_I
    letI : Fintype h.I := Fintype.ofFinite _
    (finiteEtaleMultiplicativeTrace g).hom.app (op U) (ULift.up (Additive.ofMul t)) =
      ULift.up (Additive.ofMul (∏ i,
        Units.map (sheetSection g U h rfl i).left.appTop.hom.toMonoidHom t)) := by
  let : Finite h.I := h.finite_I
  let : Fintype h.I := Fintype.ofFinite _
  change (finiteEtaleTrace g (multiplicativeSheaf.{u, 0} S)).hom.app (op U)
    (ULift.up (Additive.ofMul t)) = _
  rw [finiteEtaleTrace_app g (multiplicativeSheaf.{u, 0} S) U h]
  refine (splitTrace_apply g (multiplicativeSheaf.{u, 0} S) U h rfl
    (ULift.up (Additive.ofMul t))).trans ?_
  change (∑ i, ULift.up (Additive.ofMul
    (Units.map (sheetSection g U h rfl i).left.appTop.hom.toMonoidHom t))) = _
  apply AddEquiv.ulift.injective
  rw [map_sum]
  simp [AddEquiv.ulift]

end Stacks.EtaleCohomology
