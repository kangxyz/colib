/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.ParameterSections
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant
import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Products

/-! # Homotopy invariance under smooth parameter reindexing -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "Base(" K ")" => Spec (CommRingCat.of K)

/-- Reindexing along an additive correspondence functor with the actual
smooth parameter product on graphs preserves homotopy invariance. -/
theorem additivePrecompose_isA1Invariant
    {T : SmoothSite Base(k)} {F : Cor k ⥤ Cor k} [F.Additive]
    (e : Cor.graphFunctor k ⋙ F ≅ parameterProduct T ⋙ Cor.graphFunctor k)
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ((additivePrecompose F).obj P).IsA1Invariant := by
  intro X
  let A := SmoothSite.additiveGroupObject Base(k)
  let p := SmoothSite.productFst X A
  let V := (toPresheaf k).obj P
  let e₀ := SheafWithTransfers.parameterPrecomposeUnderlyingIso e P
  change IsIso (((toPresheaf k).obj ((additivePrecompose F).obj P)).map p.op)
  apply (NatIso.isIso_map_iff e₀ p.op).2
  change IsIso (V.map (SmoothSite.productMap p (𝟙 T)).op)
  have h : (productSwapRight X A T).hom ≫ SmoothSite.productFst (SmoothSite.product X T) A =
      SmoothSite.productMap p (𝟙 T) := productSwapRight_hom_fst X A T
  let : IsIso (V.map (SmoothSite.productFst (SmoothSite.product X T) A).op) :=
    hP (SmoothSite.product X T)
  rw [← h, op_comp, V.map_comp]
  infer_instance

end AlgebraicGeometry.PresheafWithTransfers
