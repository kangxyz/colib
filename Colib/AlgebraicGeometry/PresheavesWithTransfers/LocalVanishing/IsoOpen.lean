/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.OpenImage

/-!
# Transporting an actual affine zero open through an actual scheme isomorphism

This is the open-image part of motivic's
`OriginalEtalePresentation.exists_zero_on_original_open_of_iso`, extracted
below presentations and homotopy invariance. An actual affine zero open on
one model gives an actual affine zero open on the other, with the same marked
point and the graph-restricted section. No separatedness of the coefficient
or existence of a presentation is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]

/-- Push an actual affine zero neighborhood through the inverse of the specified iso. -/
theorem exists_affine_zero_open_of_iso
    (P : PresheafWithTransfers.{v} k) {X₀ X : SmoothSite (Spec (.of k))}
    (i : X₀ ≅ X) (v : sections P (Cor.mk X₀)) (x : X₀.left)
    (O : X.left.Opens) (hO : IsAffineOpen O) (hx : i.hom.left x ∈ O)
    (hz : transfer P ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (O.ι ≫ X.hom)) (Y := X) O.ι rfl))
        (transfer P ((Cor.graphFunctor k).map i.inv) v) = 0) :
    ∃ V : X₀.left.Opens, IsAffineOpen V ∧ x ∈ V ∧
      transfer P ((Cor.graphFunctor k).map
        (SmoothSite.homMk (X := SmoothSite.mk (V.ι ≫ X₀.hom)) (Y := X₀) V.ι rfl)) v = 0 := by
  letI : IsAffine O.toScheme := hO
  let S := SmoothSite.mk (O.ι ≫ X.hom)
  let j : S ⟶ X := SmoothSite.homMk O.ι rfl
  let f := j ≫ i.inv
  have : IsAffine S.left := hO
  have : IsOpenImmersion f.left := inferInstanceAs (IsOpenImmersion (O.ι ≫ i.inv.left))
  have hf : transfer P ((Cor.graphFunctor k).map f) v = 0 := by
    rw [Functor.map_comp, transfer_comp]
    exact hz
  refine ⟨f.left.opensRange, isAffineOpen_opensRange f.left, ?_,
    zero_on_open_image_general P f v hf⟩
  refine ⟨⟨i.hom.left x, hx⟩, ?_⟩
  exact congrArg (fun f => f.left x) i.hom_inv_id

end AlgebraicGeometry.PresheafWithTransfers
