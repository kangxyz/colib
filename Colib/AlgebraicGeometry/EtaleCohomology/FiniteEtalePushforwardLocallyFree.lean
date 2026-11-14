/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward.LocallyQConstant
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward.LocallyQConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LocallyFreeProjectionFormula
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward.OverSiteDisjointCover
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward.SplitPushforward
public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Finite étale pushforward preserves locally finite free module sheaves

The generic local-Q theorem is reused with `import all`,
just as the upstream local-Q file reuses its split-cover implementation.
No upstream files are changed and no flatness of a pushforward is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
universe u

set_option backward.isDefEq.respectTransparency false

namespace Stacks.ConstantSheaf

variable (R : Type) [CommRing R] {Y X : Scheme.{u}} (g : Y ⟶ X)
  [IsFinite g] [Etale g]
  [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]

local instance : HasLimitsOfSize.{u + 1, u + 1} (ModuleCat.{u + 1} R) :=
  ModuleCat.hasLimitsOfSize.{u + 1, u + 1, u + 1, 0} (R := R)

local instance : HasFiniteProducts (ModuleCat.{u + 1} R) := inferInstance

/-- Local coefficient predicates stable under finite products survive finite étale pushforward. -/
theorem isLocallyConstantWith_finiteEtalePushforward_modules
    (Q : ModuleCat.{u + 1} R → Prop)
    (hQ : ∀ (n : ℕ) (E : Fin n → ModuleCat.{u + 1} R),
      (∀ i, Q (E i)) → Q (Limits.piObj E))
    (F : Stacks.EtaleCohomology.EtaleModules.{u, 0} R Y)
    (hF : IsLocallyConstantWith R Y.smallEtaleTopology Q F) :
    IsLocallyConstantWith R X.smallEtaleTopology Q
      ((Stacks.EtaleCohomology.etaleModuleDirectImage.{u, 0} R g).obj F) := by
  change IsOverQConstant Q ((smallEtalePushforward g (ModuleCat.{u + 1} R)).obj F)
  exact @isOverQConstant_pushforward.{u, u + 1, u + 2} Y X g inferInstance inferInstance
    (ModuleCat.{u + 1} R) inferInstance inferInstance
    (inferInstance : ∀ U : Y.Etale,
      HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} R))
    (inferInstance : ∀ U : X.Etale,
      HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} R))
    (fun T _ => preservesFiniteProducts_constantSheaf_of_preadditive
      T.left.smallEtaleTopology (ModuleCat.{u + 1} R)) Q hQ F hF

/-- Finite products of finite free coefficient modules are finite free. -/
theorem finiteFree_piObj (n : ℕ) (E : Fin n → ModuleCat.{u + 1} R)
    (hE : ∀ i, Module.Free R (E i) ∧ Module.Finite R (E i)) :
    Module.Free R (Limits.piObj E : ModuleCat.{u + 1} R) ∧
      Module.Finite R (Limits.piObj E : ModuleCat.{u + 1} R) := by
  have : ∀ i, Module.Free R (E i) := fun i => (hE i).1
  have : ∀ i, Module.Finite R (E i) := fun i => (hE i).2
  let e := (ModuleCat.piIsoPi E).toLinearEquiv.symm
  exact ⟨Module.Free.of_equiv e, Module.Finite.of_surjective e.toLinearMap e.surjective⟩

/-- Finite étale pushforward preserves locally finite free coefficients. -/
theorem locallyFiniteFree_finiteEtalePushforward
    (F : Stacks.EtaleCohomology.EtaleModules.{u, 0} R Y)
    (hF : IsLocallyConstantWith R Y.smallEtaleTopology
      (fun E : ModuleCat.{u + 1} R => Module.Free R E ∧ Module.Finite R E) F) :
    IsLocallyConstantWith R X.smallEtaleTopology
      (fun E : ModuleCat.{u + 1} R => Module.Free R E ∧ Module.Finite R E)
      ((Stacks.EtaleCohomology.etaleModuleDirectImage.{u, 0} R g).obj F) :=
  isLocallyConstantWith_finiteEtalePushforward_modules R g _
    (finiteFree_piObj R) F hF

end Stacks.ConstantSheaf

namespace Stacks.EtaleCohomology

variable (R : Type) [CommRing R] {Y X : Scheme.{u}} (g : Y ⟶ X)
  [IsFinite g] [Etale g]

local instance (S : Scheme.{u}) (V : S.Etale) :
    HasSheafify (S.smallEtaleTopology.over V) (ModuleCat.{u + 1} R) :=
  Stacks.ConstantSheaf.hasSheafify_over_moduleCat.{u + 1, u, 0, 0}
    S.smallEtaleTopology R V

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

/-- Actual exactness for finite étale direct image of locally finite free coefficients. -/
theorem exact_tensorRight_directImage_of_locallyFiniteFree
    (G : EtaleModules.{u, 0} R Y)
    (hG : Stacks.ConstantSheaf.IsLocallyConstantWith R Y.smallEtaleTopology
      (fun E : ModuleCat.{u + 1} R => Module.Free R E ∧ Module.Finite R E) G) :
    (MonoidalCategory.tensorRight ((etaleModuleDirectImage.{u, 0} R g).obj G)).Additive ∧
    PreservesFiniteLimits
      (MonoidalCategory.tensorRight ((etaleModuleDirectImage.{u, 0} R g).obj G)) ∧
    PreservesFiniteColimits
      (MonoidalCategory.tensorRight ((etaleModuleDirectImage.{u, 0} R g).obj G)) := by
  apply additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_isLocallyConstantWith
  exact Stacks.ConstantSheaf.locallyFiniteFree_finiteEtalePushforward R g G hG

end Stacks.EtaleCohomology
