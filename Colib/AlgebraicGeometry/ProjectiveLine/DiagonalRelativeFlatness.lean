/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalSequence
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.FlatnessTransfer
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Abelian
public import Mathlib.RingTheory.Flat.Basic

/-! # Relative flatness of the diagonal quotient

The diagonal quotient is flat over the second factor. Its stalks on the diagonal
are those of the structure sheaf of the projective line, since the second
projection composed with the diagonal is the identity. Off the diagonal its
stalks vanish. Absolute flatness over the relative square is not asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Q" => (pullback π π : Scheme)
local notation "Δ" => pullback.diagonal π
local notation "p₂" => pullback.snd π π

/-- The direct image of the structure sheaf along the diagonal is flat over the second factor. -/
theorem projectiveLineDiagonalQuotient_isFlatOver :
    IsFlatOver (p₂).toLRSHom.toShHom
      ((Modules.pushforward Δ).obj (_root_.SheafOfModules.unit (P).ringCatSheaf)) := by
  let := isProper_projectiveSpaceOver 1 X
  let F := _root_.SheafOfModules.unit (P).ringCatSheaf
  have : F.IsQuasicoherent := Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit P
  intro y
  by_cases hy : y ∈ Set.range (Δ).base
  · obtain ⟨x, rfl⟩ := hy
    have hfiber : Δ ⁻¹' ({Δ x} : Set Q) = {x} := by
      ext z
      change Δ z = Δ x ↔ z = x
      exact ⟨fun hz => (Δ).isClosedEmbedding.injective hz,
        fun hz => congrArg (fun z : P => Δ z) hz⟩
    exact (isFlatOverAt_pushforward_iff Δ p₂ (𝟙 P) (pullback.diagonal_snd π) F x hfiber).mp
      ((isFlatOverAt_unit_iff_isFlatAt (𝟙 P) x).2 (Flat.stalkMap (𝟙 P) x))
  · have hzero : IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((Modules.pushforward Δ).obj F).val.presheaf y) :=
      closedInclusion_pushforward_stalk_isZero_of_not_mem_range
        (TopCat.of P) (TopCat.of Q) (Δ).base (Δ).isClosedEmbedding
        ((SheafOfModules.toSheaf (P).ringCatSheaf).obj F) y hy
    let M := TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((Modules.pushforward Δ).obj F).val.presheaf y
    let R := (P).presheaf.stalk (p₂ y)
    let : Subsingleton (↥M) := AddCommGrpCat.subsingleton_of_isZero hzero
    let : Module ((Q).presheaf.stalk y) M :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := (Q).presheaf) ((Modules.pushforward Δ).obj F).val y
    let : Module (↥R) (↥M) := Module.compHom _ ((p₂).stalkMap y).hom
    change Module.Flat (↥R) (↥M)
    have : Module.Free (↥R) (↥M) := Module.Free.of_subsingleton _ _
    exact Module.Flat.of_free

end AlgebraicGeometry.Scheme
