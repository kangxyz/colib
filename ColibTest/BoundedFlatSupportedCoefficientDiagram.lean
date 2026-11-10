/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionDiagram

/-! Fixed pullbacks, literal coefficient arrows, all realized levels and the identity algebra. -/
noncomputable section
open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.AffineOpenPair
open Topology
universe u
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

example (a : Under R) :
    (boundedAboveFlatAffineSupportedSectionModelFunctor j).obj a =
      boundedAboveFlatAffineSupportedSectionModel (inclusion j a) := rfl

example {a b : Under R} (f : a ⟶ b) :
    ((boundedAboveFlatAffineSupportedSectionModelFunctor j).map f).hom.toFunctor =
      boundedAboveFlatAffineSupportedSectionsMap (inclusion j a) (inclusion j b)
        f.right (openMap j f) (openMap_inclusion j f) := rfl

example (a : Under R) :
    (boundedAboveFlatAffineSupportedSectionModelFunctor j).map (𝟙 a) =
      𝟙 (boundedAboveFlatAffineSupportedSectionModel (inclusion j a)) :=
  (boundedAboveFlatAffineSupportedSectionModelFunctor j).map_id a

example {a b c : Under R} (f : a ⟶ b) (g : b ⟶ c) :
    (boundedAboveFlatAffineSupportedSectionModelFunctor j).map (f ≫ g) =
      (boundedAboveFlatAffineSupportedSectionModelFunctor j).map f ≫
        (boundedAboveFlatAffineSupportedSectionModelFunctor j).map g :=
  (boundedAboveFlatAffineSupportedSectionModelFunctor j).map_comp f g

example {a b : Under R} (f : a ⟶ b) (n : ℕ) :
    ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map f).map n =
      (prespectrumMap (boundedAboveFlatAffineSupportedSectionModelMap
        (inclusion j a) (inclusion j b) f.right (openMap j f)
          (openMap_inclusion j f))).map n := rfl

example {a b : Under R} (f : a ⟶ b) (n : ℕ) :
    ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map f).map (n + 1) =
      (SSet.toTop.map ((stages n).map
        (boundedAboveFlatAffineSupportedSectionModelMap
          (inclusion j a) (inclusion j b) f.right (openMap j f)
            (openMap_inclusion j f)))).hom := rfl

example {a b : Under R} (f : a ⟶ b) :
    ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map f).map 0 =
      basedLoopMap (SSet.toTop.map ((stages 0).map
        (boundedAboveFlatAffineSupportedSectionModelMap
          (inclusion j a) (inclusion j b) f.right (openMap j f)
            (openMap_inclusion j f)))).hom
        (stageMap_point 0 (boundedAboveFlatAffineSupportedSectionModelMap
          (inclusion j a) (inclusion j b) f.right (openMap j f)
            (openMap_inclusion j f))) := rfl

example (a : Under R) (n : ℕ) :
    ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map (𝟙 a)).map n =
      ContinuousMap.id _ := by
  rw [boundedAboveFlatAffineSupportedSectionPrespectrumFunctor_map_id]
  rfl

example {a b c : Under R} (f : a ⟶ b) (g : b ⟶ c) (n : ℕ) :
    ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map (f ≫ g)).map n =
      (((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map g).map n).comp
        (((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map f).map n) := by
  rw [boundedAboveFlatAffineSupportedSectionPrespectrumFunctor_map_comp]
  rfl

example :
    (boundedAboveFlatAffineSupportedSectionModelFunctor j).obj (Under.mk (𝟙 R)) =
      boundedAboveFlatAffineSupportedSectionModel (inclusion j (Under.mk (𝟙 R))) := rfl

example : openSpace j (Under.mk (𝟙 R)) ≅ U := identityProjectionIso j

example : (identityProjectionIso j).hom ≫ j = inclusion j (Under.mk (𝟙 R)) :=
  identityProjectionIso_inclusion j
