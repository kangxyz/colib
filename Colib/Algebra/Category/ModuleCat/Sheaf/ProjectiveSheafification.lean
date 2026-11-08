/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ProjectiveSections
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ObjectwiseFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification

/-!
# Flat Sheafification of Projective Module Presheaves

Projective presheaves have projective sections. Their sections are therefore flat, so the
native objectwise criterion and sheafification theorem imply flatness of the associated sheaf.
This does not assert that sheafification preserves projective objects.

This supplies the native replacement for the projective-presheaf flatness input of
`Quillen/Aglib/AlgebraicGeometry/Modules/Flat/RelativeFactorization.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The native sheafification of an actual projective presheaf of modules is flat. -/
@[stacks 03ET "Projective presheaves are objectwise flat before sheafification"]
theorem isFlat_sheafification_of_projective (O : Sheaf J CommRingCat.{w})
    (P : PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
    [Projective P] :
    AlgebraicGeometry.SheafOfModules.IsFlat (O := O)
      ((sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).obj P) := by
  let : Presheaf.IsLocallyInjective J
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :=
    Presheaf.isLocallyInjective_of_injective J _ (fun _ => Function.injective_id)
  let : Presheaf.IsLocallySurjective J
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :=
    Presheaf.isLocallySurjective_of_surjective J _ (fun _ => Function.surjective_id)
  exact Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification
    J (O := O.obj) (Osharp := O) (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) P
    (AlgebraicGeometry.SheafOfModules.PresheafOfModules.isFlat_of_objectwise_flat P
      (fun _ => inferInstance))

end PresheafOfModules
