/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleZModTraceRestriction
public import Colib.CategoryTheory.Sites.SheafPullbackNativeAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleFlatTensorExact

/-! # The actual module-sheaf tensor pairing and finite étale trace -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Functor.LaxMonoidal
universe u
namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  Stacks.SheafPushforwardMonoidal.sheafToPresheafLaxMonoidal

variable (n : ℕ) {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The actual sheaf tensorator evaluated on pure tensors of sections. -/
def zmodSheafTensorPairing (F G : EtaleModules.{u, 0} (ZMod n) X) (U : X.Etale) :
    F.obj.obj (op U) →+ G.obj.obj (op U) →+ (F ⊗ G).obj.obj (op U) := by
  let t : (TensorProduct (ZMod n) (F.obj.obj (op U)) (G.obj.obj (op U))) →ₗ[ZMod n]
      (F ⊗ G).obj.obj (op U) :=
    ((μ (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))) F G).app
      (op U)).hom
  exact LinearMap.toAddMonoidHom'.comp
    (((TensorProduct.mk (ZMod n) _ _).compr₂ t).toAddMonoidHom)

set_option backward.isDefEq.respectTransparency false in
/-- The native section tensor pairing commutes with restrictions. -/
theorem zmodSheafTensorPairing_naturality
    (F G : EtaleModules.{u, 0} (ZMod n) X) {U V : X.Etale} (k : V ⟶ U)
    (a : F.obj.obj (op U)) (b : G.obj.obj (op U)) :
    (F ⊗ G).obj.map k.op (zmodSheafTensorPairing n F G U a b) =
      zmodSheafTensorPairing n F G V (F.obj.map k.op a) (G.obj.map k.op b) := by
  have h := ConcreteCategory.congr_hom
    ((μ (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))) F G).naturality
      k.op) (a ⊗ₜ[ZMod n] b)
  exact h.symm

/-- The original finite étale module trace commutes with the actual sheaf tensor pairing
on sections. This is the pure-tensor calculation used for the native projection square. -/
theorem finiteEtaleZModRestrictionTrace_tensor_sections (g : Y ⟶ X) [Etale g] [IsFinite g]
    (F G : EtaleModules.{u, 0} (ZMod n) X) (U : X.Etale)
    (a : F.obj.obj (op U)) (b : G.obj.obj (op (baseChangeCompose g U))) :
    (finiteEtaleZModRestrictionTrace n g (F ⊗ G)).hom.app (op U)
        (zmodSheafTensorPairing n F G (baseChangeCompose g U)
          (F.obj.map (baseChangeComposeπ g U).op a) b) =
      zmodSheafTensorPairing n F G U a
        ((finiteEtaleZModRestrictionTrace n g G).hom.app (op U) b) :=
  finiteEtaleZModRestrictionTrace_pairing n g F G (F ⊗ G)
    (zmodSheafTensorPairing n F G) (fun k a b => zmodSheafTensorPairing_naturality n F G k a b)
    U a b

end Stacks.EtaleCohomology
