/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleZModRestrictionProjection

/-! # The actual trace projection formula in the restriction presentation -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Functor.LaxMonoidal
universe u
namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  Stacks.SheafPushforwardMonoidal.sheafToPresheafLaxMonoidal
  Stacks.SheafPushforwardMonoidal.pushforwardLaxMonoidal

set_option backward.isDefEq.respectTransparency false

/-- The original finite étale trace satisfies the projection formula for the actual
restriction-unit/tensorator projection morphism. -/
theorem finiteEtaleZModRestrictionProjection_trace (n : ℕ) {X Y : Scheme.{u}}
    (g : Y ⟶ X) [Etale g] [IsFinite g]
    (F G : EtaleModules.{u, 0} (ZMod n) X) :
    finiteEtaleZModRestrictionProjection n g F G ≫
        finiteEtaleZModRestrictionTrace n g (F ⊗ G) =
      F ◁ finiteEtaleZModRestrictionTrace n g G := by
  apply Stacks.SheafPushforwardMonoidal.hom_ext_tensor
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext a b
  have h := finiteEtaleZModRestrictionProjection_sections n g F G (unop U) a b
  have h₁ := congrArg
    (fun c => (finiteEtaleZModRestrictionTrace n g (F ⊗ G)).hom.app U c) h
  have h₂ := finiteEtaleZModRestrictionTrace_tensor_sections n g F G (unop U) a b
  have h₃ := zmodSheafTensorPairing_map n (𝟙 F)
    (finiteEtaleZModRestrictionTrace n g G) (unop U) a b
  simp only [id_tensorHom] at h₃
  exact (h₁.trans h₂).trans h₃.symm

end Stacks.EtaleCohomology
