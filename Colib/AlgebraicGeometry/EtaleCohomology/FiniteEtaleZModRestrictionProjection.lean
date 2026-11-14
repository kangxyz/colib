/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleZModTensorSections

/-! # The projection square in the actual restriction presentation -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale
open Functor.LaxMonoidal
universe u
namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  Stacks.SheafPushforwardMonoidal.sheafToPresheafLaxMonoidal
  Stacks.SheafPushforwardMonoidal.pushforwardLaxMonoidal

set_option backward.isDefEq.respectTransparency false

variable (n : ℕ) {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g]

/-- The actual tensor pairing is natural in both module sheaves. -/
theorem zmodSheafTensorPairing_map
    {F G F' G' : EtaleModules.{u, 0} (ZMod n) X} (f : F ⟶ F') (h : G ⟶ G')
    (U : X.Etale) (a : F.obj.obj (op U)) (b : G.obj.obj (op U)) :
    (f ⊗ₘ h).hom.app (op U) (zmodSheafTensorPairing n F G U a b) =
      zmodSheafTensorPairing n F' G' U (f.hom.app (op U) a) (h.hom.app (op U) b) := by
  have e := ConcreteCategory.congr_hom
    (NatTrans.congr_app (Functor.LaxMonoidal.μ_natural
      (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))) f h) (op U))
    (a ⊗ₜ[ZMod n] b)
  exact e.symm

omit [Etale g] in
/-- The actual direct-image tensorator on pure sections. -/
theorem etaleModuleDirectImage_tensor_sections
    (F G : EtaleModules.{u, 0} (ZMod n) Y) (U : X.Etale)
    (a : F.obj.obj (op ((smallEtaleBaseChange g).obj U)))
    (b : G.obj.obj (op ((smallEtaleBaseChange g).obj U))) :
    (μ (etaleModuleDirectImage (ZMod n) g) F G).hom.app (op U)
        (zmodSheafTensorPairing n ((etaleModuleDirectImage (ZMod n) g).obj F)
          ((etaleModuleDirectImage (ZMod n) g).obj G) U a b) =
      zmodSheafTensorPairing n F G ((smallEtaleBaseChange g).obj U) a b := by
  have e := Stacks.SheafPushforwardMonoidal.μ_sheafToPresheaf_comp_map_μ_pushforward
    X.smallEtaleTopology Y.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))
    (smallEtaleBaseChange g) F G
  have e' := ConcreteCategory.congr_hom (NatTrans.congr_app e (op U)) (a ⊗ₜ[ZMod n] b)
  exact e'

/-- The actual restriction tensorator on pure sections. -/
theorem etaleModuleRestriction_tensor_sections
    (F G : EtaleModules.{u, 0} (ZMod n) X) (V : Y.Etale)
    (a : F.obj.obj (op ((smallEtaleCompose g).obj V)))
    (b : G.obj.obj (op ((smallEtaleCompose g).obj V))) :
    (μ (etaleModuleRestriction (ZMod n) g) F G).hom.app (op V)
        (zmodSheafTensorPairing n ((etaleModuleRestriction (ZMod n) g).obj F)
          ((etaleModuleRestriction (ZMod n) g).obj G) V a b) =
      zmodSheafTensorPairing n F G ((smallEtaleCompose g).obj V) a b := by
  have e := Stacks.SheafPushforwardMonoidal.μ_sheafToPresheaf_comp_map_μ_pushforward
    Y.smallEtaleTopology X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n))
    (smallEtaleCompose g) F G
  have e' := ConcreteCategory.congr_hom (NatTrans.congr_app e (op V)) (a ⊗ₜ[ZMod n] b)
  exact e'

/-- The unit of the existing restriction adjunction on sections is base change pullback. -/
theorem etaleModuleRestriction_unit_sections
    (F : EtaleModules.{u, 0} (ZMod n) X) (U : X.Etale) (a : F.obj.obj (op U)) :
    ((etaleModuleRestrictionDirectImageAdj (ZMod n) g).unit.app F).hom.app (op U) a =
      F.obj.map (baseChangeComposeπ g U).op a := by
  rfl

/-- The canonical projection morphism expressed using the actual restriction adjunction. -/
def finiteEtaleZModRestrictionProjection
    (F G : EtaleModules.{u, 0} (ZMod n) X) :
    F ⊗ (etaleModuleDirectImage (ZMod n) g).obj
        ((etaleModuleRestriction (ZMod n) g).obj G) ⟶
      (etaleModuleDirectImage (ZMod n) g).obj
        ((etaleModuleRestriction (ZMod n) g).obj (F ⊗ G)) :=
  (etaleModuleRestrictionDirectImageAdj (ZMod n) g).unit.app F ▷ _ ≫
    μ (etaleModuleDirectImage (ZMod n) g)
      ((etaleModuleRestriction (ZMod n) g).obj F)
      ((etaleModuleRestriction (ZMod n) g).obj G) ≫
    (etaleModuleDirectImage (ZMod n) g).map
      (μ (etaleModuleRestriction (ZMod n) g) F G)

/-- On pure tensors, the canonical restriction projection is pullback in the first factor. -/
theorem finiteEtaleZModRestrictionProjection_sections
    (F G : EtaleModules.{u, 0} (ZMod n) X) (U : X.Etale)
    (a : F.obj.obj (op U)) (b : G.obj.obj (op (baseChangeCompose g U))) :
    (finiteEtaleZModRestrictionProjection n g F G).hom.app (op U)
      (zmodSheafTensorPairing n F
        ((etaleModuleDirectImage (ZMod n) g).obj
          ((etaleModuleRestriction (ZMod n) g).obj G)) U a b) =
      zmodSheafTensorPairing n F G (baseChangeCompose g U)
        (F.obj.map (baseChangeComposeπ g U).op a) b := by
  have h := zmodSheafTensorPairing_map n
    ((etaleModuleRestrictionDirectImageAdj (ZMod n) g).unit.app F)
    (𝟙 ((etaleModuleDirectImage (ZMod n) g).obj
      ((etaleModuleRestriction (ZMod n) g).obj G))) U a b
  simp only [tensorHom_id] at h
  have h₂ := etaleModuleDirectImage_tensor_sections n g
    ((etaleModuleRestriction (ZMod n) g).obj F)
    ((etaleModuleRestriction (ZMod n) g).obj G) U
    (((etaleModuleRestrictionDirectImageAdj (ZMod n) g).unit.app F).hom.app (op U) a) b
  have h₃ := etaleModuleRestriction_tensor_sections n g F G
    ((smallEtaleBaseChange g).obj U) (F.obj.map (baseChangeComposeπ g U).op a) b
  let t := (μ (etaleModuleRestriction (ZMod n) g) F G).hom.app
    (op ((smallEtaleBaseChange g).obj U))
  let r := (μ (etaleModuleDirectImage (ZMod n) g)
    ((etaleModuleRestriction (ZMod n) g).obj F)
    ((etaleModuleRestriction (ZMod n) g).obj G)).hom.app (op U)
  have e₁ := congrArg (fun c => t (r c)) h
  have e₂ := congrArg (fun c => t c) h₂
  exact e₁.trans (e₂.trans h₃)

end Stacks.EtaleCohomology
