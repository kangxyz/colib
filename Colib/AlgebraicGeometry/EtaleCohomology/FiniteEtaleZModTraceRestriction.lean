/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleZModTrace
public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleTracePairing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage

/-!
# The actual trace and the restriction presentation

This identifies the existing native trace with the original finite étale trace in the
restriction presentation, using the canonical comparison of the same two left adjoints.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u
namespace Stacks.EtaleCohomology

variable (n : ℕ) {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g]

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting the native module-to-restriction comparison gives the canonical abelian
comparison, transported through the actual coefficient forgetful comparison. -/
theorem forget_inverseImageRestrictionIso_hom (M : EtaleModules.{u, 0} (ZMod n) X) :
    (etaleModuleForgetAb (ZMod n) Y).map
        ((etaleModuleInverseImageRestrictionIso (ZMod n) g).hom.app M) =
      (traceForgetPullbackAbIso (ZMod n) g).inv.app M ≫
        ((smallEtaleAdjunctionAb g).leftAdjointUniq
          (etaleRestrictionAbelianDirectImageAdj.{u, 0} g)).hom.app
          ((etaleModuleForgetAb (ZMod n) X).obj M) := by
  have h := congrArg ((etaleModuleForgetAb (ZMod n) X).map)
    (Adjunction.unit_leftAdjointUniq_hom_app
      (etaleModuleInverseImageAdj (ZMod n) g)
      (etaleModuleRestrictionDirectImageAdj (ZMod n) g) M)
  simp only [Functor.map_comp] at h
  rw [traceForgetPullbackAbIso_unit] at h
  have hunit : (etaleModuleForgetAb (ZMod n) X).map
      ((etaleModuleRestrictionDirectImageAdj (ZMod n) g).unit.app M) =
      (etaleRestrictionAbelianDirectImageAdj.{u, 0} g).unit.app
        ((etaleModuleForgetAb (ZMod n) X).obj M) := by
    rfl
  rw [hunit] at h
  change ((smallEtaleAdjunctionAb g).unit.app ((etaleModuleForgetAb (ZMod n) X).obj M) ≫
      (smallEtalePushforwardAb g).map ((traceForgetPullbackAbIso (ZMod n) g).hom.app M)) ≫
      (smallEtalePushforwardAb g).map ((etaleModuleForgetAb (ZMod n) Y).map
        ((etaleModuleInverseImageRestrictionIso (ZMod n) g).hom.app M)) = _ at h
  apply (cancel_epi ((traceForgetPullbackAbIso (ZMod n) g).hom.app M)).mp
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  apply ((smallEtaleAdjunctionAb g).homEquiv _ _).injective
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simpa only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc] using h

variable [IsFinite g]

/-- The original finite étale trace lifted to Z/n-module sheaves in its restriction
presentation. Its underlying abelian map is the existing trace, not a replacement. -/
def finiteEtaleZModRestrictionTrace (M : EtaleModules.{u, 0} (ZMod n) X) :
    (etaleModuleDirectImage (ZMod n) g).obj
      ((etaleModuleRestriction (ZMod n) g).obj M) ⟶ M :=
  (etaleModuleForgetAbZModFullyFaithful n X).preimage
    (finiteEtaleTrace g ((etaleModuleForgetAb (ZMod n) X).obj M))

/-- Forgetting this module morphism recovers exactly the original abelian trace. -/
theorem forget_finiteEtaleZModRestrictionTrace (M : EtaleModules.{u, 0} (ZMod n) X) :
    (etaleModuleForgetAb (ZMod n) X).map (finiteEtaleZModRestrictionTrace n g M) =
      finiteEtaleTrace g ((etaleModuleForgetAb (ZMod n) X).obj M) :=
  (etaleModuleForgetAbZModFullyFaithful n X).map_preimage _

set_option backward.isDefEq.respectTransparency false in
/-- The actual native trace is the original restriction trace composed with the canonical
inverse-image comparison. -/
theorem finiteEtaleZModTrace_eq_restriction (M : EtaleModules.{u, 0} (ZMod n) X) :
    finiteEtaleZModTrace n g M =
      (etaleModuleDirectImage (ZMod n) g).map
          ((etaleModuleInverseImageRestrictionIso (ZMod n) g).hom.app M) ≫
        finiteEtaleZModRestrictionTrace n g M := by
  apply (etaleModuleForgetAb (ZMod n) X).map_injective
  rw [forget_finiteEtaleZModTrace, Functor.map_comp, forget_finiteEtaleZModRestrictionTrace]
  change _ = (smallEtalePushforwardAb g).map
    ((etaleModuleForgetAb (ZMod n) Y).map
      ((etaleModuleInverseImageRestrictionIso (ZMod n) g).hom.app M)) ≫ _
  rw [forget_inverseImageRestrictionIso_hom]
  simp only [finiteEtaleTraceOnPullbackAb, Functor.map_comp, Category.assoc]

/-- The original module restriction trace obeys the sectionwise projection identity for
any natural biadditive pairing of the given module sheaves. -/
theorem finiteEtaleZModRestrictionTrace_pairing
    (F G H : EtaleModules.{u, 0} (ZMod n) X)
    (b : ∀ U : X.Etale, (F.obj.obj (Opposite.op U)) →+
      (G.obj.obj (Opposite.op U)) →+ (H.obj.obj (Opposite.op U)))
    (hb : ∀ {U V : X.Etale} (k : V ⟶ U)
      (a : F.obj.obj (Opposite.op U)) (c : G.obj.obj (Opposite.op U)),
      H.obj.map k.op (b U a c) =
        b V (F.obj.map k.op a) (G.obj.map k.op c))
    (U : X.Etale) (a : F.obj.obj (Opposite.op U))
    (c : G.obj.obj (Opposite.op (baseChangeCompose g U))) :
    (finiteEtaleZModRestrictionTrace n g H).hom.app (Opposite.op U)
        (b (baseChangeCompose g U) (F.obj.map (baseChangeComposeπ g U).op a) c) =
      b U a ((finiteEtaleZModRestrictionTrace n g G).hom.app (Opposite.op U) c) := by
  change ((etaleModuleForgetAb (ZMod n) X).map
      (finiteEtaleZModRestrictionTrace n g H)).hom.app (Opposite.op U) _ =
    b U a (((etaleModuleForgetAb (ZMod n) X).map
      (finiteEtaleZModRestrictionTrace n g G)).hom.app (Opposite.op U) c)
  rw [forget_finiteEtaleZModRestrictionTrace, forget_finiteEtaleZModRestrictionTrace]
  exact finiteEtaleTrace_pairing g
    ((etaleModuleForgetAb (ZMod n) X).obj F)
    ((etaleModuleForgetAb (ZMod n) X).obj G)
    ((etaleModuleForgetAb (ZMod n) X).obj H) b hb U a c

end Stacks.EtaleCohomology
