/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.FiniteEtaleTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleModulesZModTorsion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars

/-!
# The actual finite étale trace with Z/n coefficients

This file lifts the existing abelian finite étale trace through the fully faithful
forgetful functor. It uses the original inverse image, not a replacement coefficient model.
No Ext projection formula or norm-residue claim is made here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section Comparison

variable (Λ : Type) [CommRing Λ]

/-- Postcomposition with the forgetful functor carries sheaves of modules to abelian sheaves. -/
local instance (Z : Scheme.{u}) : Z.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ Z.smallEtaleTopology

/-- Sheafification commutes with forgetting the module structure. -/
local instance (Z : Scheme.{u}) : Z.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  ModuleSheaf.preservesSheafification_forget₂.{u + 1} Λ Z.smallEtaleTopology



/-! ### Forgetting the module structure and inverse image -/



variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- **Inverse image commutes with forgetting the module structure**, the inverse image of abelian
sheaves being `Stacks.EtaleCohomology.smallEtalePullbackAb`: the mate of the strict commutation
of direct image with forgetting the module structure. -/
def traceForgetPullbackAbIso :
    etaleModuleForgetAb.{u, 0} Λ X ⋙ smallEtalePullbackAb g ≅
      etaleModuleInverseImage.{u, 0} Λ g ⋙ etaleModuleForgetAb.{u, 0} Λ Y :=
  asIso (coefficientSheafPullbackTwoSquare (smallEtaleBaseChange g) X.smallEtaleTopology
    Y.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))

/-- **The comparison matches the units** of the inverse image adjunctions of sheaves of modules
and of abelian sheaves. -/
theorem traceForgetPullbackAbIso_unit (M : EtaleModules.{u, 0} Λ X) :
    (etaleModuleForgetAb.{u, 0} Λ X).map ((etaleModuleInverseImageAdj.{u, 0} Λ g).unit.app M) =
      (smallEtaleAdjunctionAb g).unit.app ((etaleModuleForgetAb.{u, 0} Λ X).obj M) ≫
        (smallEtalePushforwardAb g).map ((traceForgetPullbackAbIso Λ g).hom.app M) :=
  coefficientSheafPullbackTwoSquare_unit (smallEtaleBaseChange g) X.smallEtaleTopology
    Y.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) M


end Comparison

variable (n : ℕ) {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g] [IsFinite g]

/-- Transport the existing abelian trace from restriction to the original inverse image. -/
def finiteEtaleTraceOnPullbackAb
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (smallEtalePushforwardAb g).obj ((smallEtalePullbackAb g).obj G) ⟶ G :=
  (smallEtalePushforwardAb g).map
      (((smallEtaleAdjunctionAb g).leftAdjointUniq
        (etaleRestrictionAbelianDirectImageAdj.{u, 0} g)).hom.app G) ≫
    finiteEtaleTrace g G

/-- The actual module trace, lifting the original abelian trace via fully faithful forgetting. -/
def finiteEtaleZModTrace (M : EtaleModules.{u, 0} (ZMod n) X) :
    (etaleModuleDirectImage.{u, 0} (ZMod n) g).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod n) g).obj M) ⟶ M :=
  (etaleModuleForgetAbZModFullyFaithful n X).preimage
    ((smallEtalePushforwardAb g).map
        ((traceForgetPullbackAbIso (ZMod n) g).inv.app M) ≫
      finiteEtaleTraceOnPullbackAb g ((etaleModuleForgetAb.{u, 0} (ZMod n) X).obj M))

/-- Forgetting the module trace recovers the specified transported abelian trace. -/
theorem forget_finiteEtaleZModTrace (M : EtaleModules.{u, 0} (ZMod n) X) :
    (etaleModuleForgetAb.{u, 0} (ZMod n) X).map (finiteEtaleZModTrace n g M) =
      (smallEtalePushforwardAb g).map
          ((traceForgetPullbackAbIso (ZMod n) g).inv.app M) ≫
        finiteEtaleTraceOnPullbackAb g
          ((etaleModuleForgetAb.{u, 0} (ZMod n) X).obj M) :=
  (etaleModuleForgetAbZModFullyFaithful n X).map_preimage _

/-- Unit followed by the transported original abelian trace is the degree. -/
theorem unit_comp_finiteEtaleTraceOnPullbackAb
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {d : ℕ}
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank g d] :
    (smallEtaleAdjunctionAb g).unit.app G ≫ finiteEtaleTraceOnPullbackAb g G =
      d • 𝟙 G := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ finiteEtaleTrace g G)
      (Adjunction.unit_leftAdjointUniq_hom_app (smallEtaleAdjunctionAb g)
        (etaleRestrictionAbelianDirectImageAdj.{u, 0} g) G)).trans
      (unit_comp_finiteEtaleTrace g G))

set_option backward.isDefEq.respectTransparency false in
/-- Unit followed by the actual module trace is the degree. -/
theorem unit_comp_finiteEtaleZModTrace (M : EtaleModules.{u, 0} (ZMod n) X)
    {d : ℕ} [Stacks.Morphisms.IsFiniteLocallyFreeOfRank g d] :
    (etaleModuleInverseImageAdj.{u, 0} (ZMod n) g).unit.app M ≫
      finiteEtaleZModTrace n g M = d • 𝟙 M := by
  apply (etaleModuleForgetAbZModFullyFaithful n X).map_injective
  rw [Functor.map_comp, forget_finiteEtaleZModTrace,
    traceForgetPullbackAbIso_unit]
  let P := smallEtalePushforwardAb g
  let e := traceForgetPullbackAbIso (ZMod n) g
  have hc : P.map (e.hom.app M) ≫ P.map (e.inv.app M) = 𝟙 _ :=
    (P.map_comp _ _).symm.trans
      ((congrArg P.map (e.hom_inv_id_app M)).trans (P.map_id _))
  have ht := congrArg
    ((smallEtaleAdjunctionAb g).unit.app
      ((etaleModuleForgetAb (ZMod n) X).obj M) ≫ ·)
    ((Category.assoc (P.map (e.hom.app M)) (P.map (e.inv.app M))
      (finiteEtaleTraceOnPullbackAb g
        ((etaleModuleForgetAb (ZMod n) X).obj M))).symm.trans
      ((congrArg (· ≫ finiteEtaleTraceOnPullbackAb g
        ((etaleModuleForgetAb (ZMod n) X).obj M)) hc).trans (Category.id_comp _)))
  exact (Category.assoc _ _ _).trans (ht.trans
    ((unit_comp_finiteEtaleTraceOnPullbackAb g _).trans
      ((Functor.map_nsmul (etaleModuleForgetAb (ZMod n) X)).trans
        (congrArg (d • ·) ((etaleModuleForgetAb (ZMod n) X).map_id M))).symm))

end Stacks.EtaleCohomology
