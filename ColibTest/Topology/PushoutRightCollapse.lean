/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.Topology.Prespectrum.PushoutRightInclusionStable
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.LoopPrespectrum.PushoutRightCollapseTest

namespace T0
open HomotopyPushout
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)
example :
    rightConeRebracket f g ≫ rightConeRebracketInv f g = 𝟙 (mappingCone (inr f g)) :=
  rightConeRebracket_hom_inv f g
end T0

namespace T1
open HomotopyPushout
variable {A B : LoopPrespectrum.{u}} (f : A ⟶ B)
example : pointConeMap f ≫ pointConeInv f =
    𝟙 (prespectrum f (zeroHom A pointPrespectrum)) :=
  pointCone_hom_inv f
end T1

namespace T2
variable (E : LoopPrespectrum.{u})
example (d : ℤ) :
    Subsingleton (stableHomotopyGroup (mappingCone (𝟙 E)) d) :=
  mappingCone_id_stableHomotopyGroup_subsingleton E d
end T2

namespace T3
open HomotopyPushout
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)
example :
    rightConeCollapse f g = rightConeRebracket f g ≫ rightConePointMap f g ≫ pointConeMap f :=
  rightConeCollapse_factor f g
end T3

namespace T4
example
    {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (hf : IsStableEquivalence (mappingConeFiberComparison f))
    (hcone : ∀ d : ℤ, Subsingleton (stableHomotopyGroup (mappingCone f) d)) :
    IsStableEquivalence f :=
  isStableEquivalence_of_cone_stableGroup_subsingleton f hf hcone
end T4

namespace T5
open HomotopyPushout
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)
example
    (hA : ∀ n, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A.point (n + 1)))))
    (hB : ∀ n, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B.point (n + 1)))))
    (hC : ∀ n, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (C.point (n + 1)))))
    (he : IsStableEquivalence (mappingConeFiberComparison f))
    (hi : IsStableEquivalence (mappingConeFiberComparison (inr f g)))
    (hf : IsStableEquivalence f) : IsStableEquivalence (inr f g) :=
  inr_isStableEquivalence_of_excision f g hA hB hC he hi hf
end T5

end Topology.LoopPrespectrum.PushoutRightCollapseTest

namespace PositiveLevelConsumer
open CategoryTheory Topology
example {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (hf : ∀ n, IsWeakHomotopyEquivalence (f.map (n + 1))) :
    LoopPrespectrum.IsStableEquivalence f :=
  LoopPrespectrum.isStableEquivalence_of_positiveLevel f hf
end PositiveLevelConsumer
