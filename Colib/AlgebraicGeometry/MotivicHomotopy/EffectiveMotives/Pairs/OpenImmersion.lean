/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Representable
import Colib.AlgebraicGeometry.Chow.PolynomialCurveCycles
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
# Open immersions on transfer representables

The graph of an open immersion preserves each signed coefficient at its
image point. Its map on presheaves with transfers is objectwise injective,
and exact Nisnevich sheafification retains the monomorphism.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The sheafified signed graph of an open immersion is mono on transfer representables. -/
instance mono_transferRepresentable_map_openImmersion
    {U X : SmoothSite (Spec (.of k))} (j : U ⟶ X) [IsOpenImmersion j.left] :
    Mono ((transferRepresentable k).map ((Cor.graphFunctor k).map j)) := by
  let f := (representableLarge k).map ((Cor.graphFunctor k).map j)
  let U : PresheafWithTransfers.{u + 1} k ⥤ (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    PresheafWithTransfers.forget
  let : U.ReflectsMonomorphisms := Functor.reflectsMonomorphisms_of_faithful U
  have hmono (T : (Cor k)ᵒᵖ) : Mono ((U.map f).app T) := by
    apply (AddCommGrpCat.mono_iff_injective _).2
    rintro ⟨α⟩ ⟨β⟩ h
    have he : α ≫ (Cor.graphFunctor k).map j = β ≫ (Cor.graphFunctor k).map j :=
      congrArg ULift.down h
    exact congrArg ULift.up (PolynomialCurveCycles.openGraph_injective k j he)
  let : ∀ T : (Cor k)ᵒᵖ, Mono ((U.map f).app T) := hmono
  let : Mono f := U.mono_of_mono_map (NatTrans.mono_of_mono_app (U.map f))
  let A := nisnevichSheafify k
  exact preserves_mono_of_preservesLimit A f

end AlgebraicGeometry.SheafWithTransfers
