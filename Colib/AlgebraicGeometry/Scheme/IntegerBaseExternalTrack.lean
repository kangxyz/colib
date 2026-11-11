/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.Scheme.IntegerBaseExternalFactor

/-!
# Transported external tracks on a two-factor raw cell

A genuine natural
transformation into the external-factor diagram commutes with internal interchange after the
actual inverse two-swap transport. Time slices of a natural homotopy are direct consumers.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u v w
namespace AlgebraicGeometry.Scheme.Products
variable {S T U : Scheme.{u}}

/-- The original two-lift swap is already the component of the original product isomorphism. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Products/IntegerBaseExternalTrack.lean:27"
  "adaptation" "Original literal three-factor swaps and whole external transport."]
instance baseProductSwapMap_isIso (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (X : Scheme.{u}) : IsIso (baseProductSwapMap p q X) := by
  change IsIso ((baseProductSwapIso p q).hom.app X)
  infer_instance

/-- Moving the external factor is a composite of the original two isomorphisms. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Products/IntegerBaseExternalTrack.lean:33"
  "adaptation" "Original literal three-factor swaps and whole external transport."]
instance baseProductMoveExternal_isIso (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (r : U ⟶ (Spec (.of (ULift.{u} ℤ)))) (X : Scheme.{u}) :
    IsIso (baseProductMoveExternal p q r X) := by
  dsimp only [baseProductMoveExternal]
  infer_instance

/-- A raw cell's external track, transported with the inverse of the actual geometric move. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Products/IntegerBaseExternalTrack.lean:39"
  "adaptation" "Original literal three-factor swaps and whole external transport."]
def baseProductExternalTrack {C : Type v} [Category.{w} C]
    (F : Scheme.{u}ᵒᵖ ⥤ C) (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (r : U ⟶ (Spec (.of (ULift.{u} ℤ)))) (τ : F ⟶ (baseProductFunctor r).op ⋙ F) (X : Scheme.{u}) :
    F.obj (op ((baseProductFunctor q).obj ((baseProductFunctor p).obj X))) ⟶
      F.obj (op ((baseProductFunctor q).obj
        ((baseProductFunctor p).obj ((baseProductFunctor r).obj X)))) :=
  τ.app _ ≫ F.map (inv (baseProductMoveExternal p q r X).op)

/-- Naturality and the actual braid give the transported whole external-track square. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Products/IntegerBaseExternalTrack.lean:48"
  "adaptation" "Original literal three-factor swaps and whole external transport."]
theorem baseProductExternalTrack_swap {C : Type v} [Category.{w} C]
    (F : Scheme.{u}ᵒᵖ ⥤ C) (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (r : U ⟶ (Spec (.of (ULift.{u} ℤ)))) (τ : F ⟶ (baseProductFunctor r).op ⋙ F) (X : Scheme.{u}) :
    F.map (baseProductSwapMap p q X).op ≫ baseProductExternalTrack F p q r τ X =
      baseProductExternalTrack F q p r τ X ≫
        F.map (baseProductSwapMap p q ((baseProductFunctor r).obj X)).op := by
  apply (cancel_mono (F.map (baseProductMoveExternal p q r X).op)).1
  dsimp only [baseProductExternalTrack]
  simp only [Category.assoc, ← F.map_comp, IsIso.inv_hom_id, F.map_id]
  rw [← baseProductMoveExternal_swap_op]
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  exact (Category.comp_id _).trans (τ.naturality (baseProductSwapMap p q X).op)

end AlgebraicGeometry.Scheme.Products
