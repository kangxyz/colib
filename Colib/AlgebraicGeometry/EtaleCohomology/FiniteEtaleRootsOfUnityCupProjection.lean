/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleZModCupProjection
public import Colib.AlgebraicGeometry.EtaleCohomology.InverseImageLocallyFree

/-!
# The actual roots-of-unity Ext cup projection formula

All three tensor exactness requirements are proved for the actual roots-of-unity
coefficient, its native inverse image and its native finite étale direct image.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory
open AlgebraicGeometry
open Functor.LaxMonoidal
universe w u
namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  Stacks.SheafPushforwardMonoidal.pushforwardLaxMonoidal
  etaleModuleInverseImageSheafPullbackMonoidal
  finiteEtaleZModDirectImage_preservesFiniteColimits
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} {k : Type u} [Field k]
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) [Etale g] [IsFinite g]
  (N : ℕ) [NeZero N] [NeZero (N : k)]
  [HasExt.{w} (EtaleModules.{u, 0} (ZMod N) X)]
  [HasExt.{w} (EtaleModules.{u, 0} (ZMod N) Y)]
  [EnoughInjectives (EtaleModules.{u, 0} (ZMod N) X)]
  [EnoughInjectives (EtaleModules.{u, 0} (ZMod N) Y)]

/-- The finite étale projection formula with the original μ_N as second coefficient,
in arbitrary degrees. No tensor exactness or projection formula is assumed. -/
theorem finiteEtaleRootsOfUnityUnitCorestriction_cup
    (F : EtaleModules.{u, 0} (ZMod N) X) {i j d : ℕ} (h : j + i = d)
    (a : Ext.{w} (𝟙_ (EtaleModules.{u, 0} (ZMod N) X)) F i)
    (b : Ext.{w} (𝟙_ (EtaleModules.{u, 0} (ZMod N) Y))
      ((etaleModuleInverseImage (ZMod N) g).obj
        (Stacks.Kummer.rootsOfUnityModule.{u, 0} X N)) j) :
    let G := Stacks.Kummer.rootsOfUnityModule.{u, 0} X N
    let hG :=
      additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_isLocallyConstantWith
        (Λ := ZMod N) G (Stacks.Kummer.locallyFiniteFree_rootsOfUnityModule f N)
    letI := hG.1
    letI := hG.2.1
    letI := hG.2.2
    let hLG := additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_inverseImage
      (Λ := ZMod N) g G (Stacks.Kummer.locallyFiniteFree_rootsOfUnityModule f N)
    letI := hLG.1
    letI := hLG.2.1
    letI := hLG.2.2
    finiteEtaleZModUnitCorestriction N g (F ⊗ G) d
      (Stacks.ExtCup.cup (μ (etaleModuleInverseImage (ZMod N) g) F G)
        (Stacks.ExtCup.mapUnit (etaleModuleInverseImage (ZMod N) g) a) b h) =
      Stacks.ExtCup.cup (𝟙 (F ⊗ G)) a
        (finiteEtaleZModUnitCorestriction N g G j b) h := by
  let G := Stacks.Kummer.rootsOfUnityModule.{u, 0} X N
  obtain ⟨hG₁, hG₂, hG₃⟩ :=
    additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_isLocallyConstantWith
      (Λ := ZMod N) G (Stacks.Kummer.locallyFiniteFree_rootsOfUnityModule f N)
  obtain ⟨hLG₁, hLG₂, hLG₃⟩ :=
    additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_inverseImage
      (Λ := ZMod N) g G (Stacks.Kummer.locallyFiniteFree_rootsOfUnityModule f N)
  obtain ⟨hRLG₁, hRLG₂, hRLG₃⟩ :=
    Colib.EtaleLocallyFree.exact_tensorRight_pushforward_pullback_rootsOfUnityModule f g N
  exact finiteEtaleZModUnitCorestriction_cup N g F G h a b

end Stacks.EtaleCohomology
