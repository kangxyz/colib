/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.AffineBaseChange
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionModel

/-!
# The actual supported section diagram over a fixed original affine open

Each algebra over R uses the one specified pullback of the original open j. Its original
coefficient arrows induce the exact supported Model maps already constructed. Their genuine
identity/composition laws and the literal fixed-endpoint pullback equations give a strict diagram.
The identity-algebra object is still its actual pullback; it has not been identified with j.
Adapted from Quillen `BoundedFlat/SupportedSectionDiagram.lean:28-71` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry.Scheme.AffineOpenPair
open CategoryTheory.Waldhausen.SmallWaldhausenCategory Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- For fixed original coefficient map, support witnesses do not change the actual Model arrow. -/
theorem boundedAboveFlatAffineSupportedSectionModelMap_openMap_irrel
    {S : CommRingCat.{u}} {V : Scheme.{u}} (j' : V ⟶ Spec S) [IsOpenImmersion j']
    (f : R ⟶ S) (l l' : V ⟶ U)
    (h : l ≫ j = j' ≫ Spec.map f) (h' : l' ≫ j = j' ≫ Spec.map f) :
    boundedAboveFlatAffineSupportedSectionModelMap j j' f l h =
      boundedAboveFlatAffineSupportedSectionModelMap j j' f l' h' := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  rfl

/-- The original supported models on fixed pullbacks form a genuine coefficient diagram. -/
def boundedAboveFlatAffineSupportedSectionModelFunctor :
    Under R ⥤ WideSubcategory preservesZero.{u + 1} where
  obj a := boundedAboveFlatAffineSupportedSectionModel (inclusion j a)
  map {a b} f := boundedAboveFlatAffineSupportedSectionModelMap
    (inclusion j a) (inclusion j b) f.right (openMap j f) (openMap_inclusion j f)
  map_id a := by
    have h : 𝟙 (openSpace j a) ≫ inclusion j a =
        inclusion j a ≫ Spec.map (𝟙 a.right) := by simp
    exact (boundedAboveFlatAffineSupportedSectionModelMap_openMap_irrel
      (inclusion j a) (inclusion j a) (𝟙 a.right) (openMap j (𝟙 a)) (𝟙 _)
      (openMap_inclusion j (𝟙 a)) h).trans
        (boundedAboveFlatAffineSupportedSectionModelMap_id (inclusion j a) h)
  map_comp {a b c} f g := by
    have h : (openMap j g ≫ openMap j f) ≫ inclusion j a =
        inclusion j c ≫ Spec.map (f.right ≫ g.right) := by
      rw [← openMap_comp]
      exact openMap_inclusion j (f ≫ g)
    exact (boundedAboveFlatAffineSupportedSectionModelMap_openMap_irrel
      (inclusion j a) (inclusion j c) (f.right ≫ g.right)
      (openMap j (f ≫ g)) (openMap j g ≫ openMap j f)
      (openMap_inclusion j (f ≫ g)) h).trans
        (boundedAboveFlatAffineSupportedSectionModelMap_comp
          (inclusion j a) (inclusion j b) (inclusion j c) f.right g.right
          (openMap j f) (openMap j g) (openMap_inclusion j f) (openMap_inclusion j g) h)

/-- Apply the actual original iterated-S realization to the strict supported Model diagram. -/
def boundedAboveFlatAffineSupportedSectionPrespectrumFunctor : Under R ⥤ LoopPrespectrum.{u + 1} :=
  boundedAboveFlatAffineSupportedSectionModelFunctor j ⋙ prespectrumFunctor

/-- Every diagram arrow is the unchanged original supported coefficient prespectrum map. -/
theorem boundedAboveFlatAffineSupportedSectionPrespectrumFunctor_map
    {a b : Under R} (f : a ⟶ b) :
    (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map f =
      boundedAboveFlatAffineSupportedSectionPrespectrumMap
        (inclusion j a) (inclusion j b) f.right (openMap j f) (openMap_inclusion j f) := rfl

/-- Whole prespectrum identity is literal, before taking homotopy classes. -/
theorem boundedAboveFlatAffineSupportedSectionPrespectrumFunctor_map_id (a : Under R) :
    (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map (𝟙 a) =
      𝟙 ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).obj a) :=
  (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map_id a

/-- Whole prespectrum composition retains the actual coefficient arrows. -/
theorem boundedAboveFlatAffineSupportedSectionPrespectrumFunctor_map_comp
    {a b c : Under R} (f : a ⟶ b) (g : b ⟶ c) :
    (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map (f ≫ g) =
      (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map f ≫
        (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map g :=
  (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map_comp f g

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0501", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedSectionDiagram.lean:28-71"
  "adaptation"
  "The actual fixed-pullback `Under R` model diagram and its iterated-S prespectrum functor"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionModelFunctor
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionPrespectrumFunctor
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionPrespectrumFunctor_map
