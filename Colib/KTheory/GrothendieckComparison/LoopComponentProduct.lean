/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.KTheory.GrothendieckComparison.ContinuousLoopLabels
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.NormalizedComponentProduct

/-!
# An actual normalized original Q-loop component product

The discrete labels are the unchanged homotopical K₀ classes. Representatives
are chosen only after the actual classifier and its surjectivity are proved;
the neutral representative is literally the original constant loop. The
product has that exact component inclusion on its neutral slice, and ordinary
representative-independence and exact-functor naturality homotopies. This does
not identify the neutral component with any plus construction.
-/

open Topology CategoryTheory

/-! Implementation source: `Quillen/KTheory/GrothendieckComparison/LoopComponentProduct.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and original proofs are retained. -/

@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval
universe u v
namespace CategoryTheory.ExactCategory.ExactStructure
open Topology CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- The actual constant-loop path component of the unchanged Q based loop space. -/
abbrev QLoopIdentityComponent := pathComponent (Path.refl E.kBasepoint)

/-- Representatives chosen in the original loop space, exactly constant at the neutral label. -/
def qLoopRepresentative (a : E.DiscreteKZero) : Path E.kBasepoint E.kBasepoint := by
  classical
  exact if a = E.discreteKZeroIdentity then Path.refl E.kBasepoint
    else (E.loopKZeroLabel_surjective a).choose

/-- Every chosen representative has its specified original K₀ label. -/
theorem qLoopRepresentative_label (a : E.DiscreteKZero) :
    E.loopKZeroLabel (E.qLoopRepresentative a) = a := by
  classical
  by_cases ha : a = E.discreteKZeroIdentity
  · subst a
    simpa only [qLoopRepresentative, ite_true] using E.loopKZeroLabel_refl
  · simpa only [qLoopRepresentative, ha, ite_false] using
      (E.loopKZeroLabel_surjective a).choose_spec

/-- Neutral normalization is an equality of actual original loops. -/
theorem qLoopRepresentative_identity :
    E.qLoopRepresentative E.discreteKZeroIdentity = Path.refl E.kBasepoint := by
  classical
  simp only [qLoopRepresentative, ite_true]

/-- The classifier fibers are precisely the components of these actual representatives. -/
theorem loopKZeroLabel_fiber (a : E.DiscreteKZero)
    (γ : Path E.kBasepoint E.kBasepoint) :
    E.continuousLoopKZeroLabel γ = a ↔ Joined (E.qLoopRepresentative a) γ := by
  change E.loopKZeroLabel γ = a ↔ _
  constructor
  · intro h
    exact (E.loopKZeroLabel_eq_iff _ _).mp ((E.qLoopRepresentative_label a).trans h.symm)
  · intro h
    exact ((E.loopKZeroLabel_eq_iff _ _).mpr h).symm.trans (E.qLoopRepresentative_label a)

/-- The genuine product-to-loop equivalence, exactly normalized on the neutral slice. -/
def qLoopComponentProductEquiv :
    ContinuousMap.HomotopyEquiv (E.DiscreteKZero × E.QLoopIdentityComponent)
      (Path E.kBasepoint E.kBasepoint) :=
  normalizedLoopComponentProductEquiv E.continuousLoopKZeroLabel E.discreteKZeroIdentity
    E.qLoopRepresentative E.loopKZeroLabel_fiber E.qLoopRepresentative_identity

/-- The requested original-loop-to-product direction of the same genuine homotopy equivalence. -/
def qLoopProductEquiv :
    ContinuousMap.HomotopyEquiv (Path E.kBasepoint E.kBasepoint)
      (E.DiscreteKZero × E.QLoopIdentityComponent) := E.qLoopComponentProductEquiv.symm

/-- The neutral slice is exactly the original identity-component inclusion. -/
theorem qLoopComponentProductEquiv_identity (z : E.QLoopIdentityComponent) :
    E.qLoopComponentProductEquiv (E.discreteKZeroIdentity, z) = z.val :=
  normalizedLoopComponentProductMap_zero _ _ z

/-- Away from the neutral slice the forward map is literal right concatenation. -/
theorem qLoopComponentProductEquiv_of_ne (a : E.DiscreteKZero)
    (ha : a ≠ E.discreteKZeroIdentity) (z : E.QLoopIdentityComponent) :
    E.qLoopComponentProductEquiv (a, z) = z.val.trans (E.qLoopRepresentative a) := by
  classical
  simp only [qLoopComponentProductEquiv, normalizedLoopComponentProductEquiv_toFun,
    normalizedLoopComponentProductMap, ContinuousMap.coe_mk, ha, ite_false]

/-- The product coordinate is the original K₀ label, with no permutation or sign change. -/
theorem qLoopProductEquiv_label (γ : Path E.kBasepoint E.kBasepoint) :
    (E.qLoopProductEquiv γ).1 = E.continuousLoopKZeroLabel γ :=
  normalizedLoopComponentProductEquiv_inverse_label E.continuousLoopKZeroLabel
    E.discreteKZeroIdentity E.qLoopRepresentative E.loopKZeroLabel_fiber
    E.qLoopRepresentative_identity γ

/-- Any other correctly labeled representatives are joined by actual paths of original loops. -/
def qLoopRepresentativePath (r : E.DiscreteKZero → Path E.kBasepoint E.kBasepoint)
    (hr : ∀ a, E.loopKZeroLabel (r a) = a) (a : E.DiscreteKZero) :
    Path (E.qLoopRepresentative a) (r a) :=
  ((E.loopKZeroLabel_eq_iff _ _).mp ((E.qLoopRepresentative_label a).trans (hr a).symm)).somePath

/-- Changing representatives gives an actual homotopy, constant on the entire neutral slice. -/
def qLoopComponentProductChoiceHomotopy
    (r : E.DiscreteKZero → Path E.kBasepoint E.kBasepoint)
    (hr : ∀ a, E.loopKZeroLabel (r a) = a) :
    E.qLoopComponentProductEquiv.toFun.Homotopy
      (normalizedLoopComponentProductMap E.discreteKZeroIdentity r) :=
  normalizedLoopComponentProductHomotopy E.discreteKZeroIdentity
    (E.qLoopRepresentativePath r hr)

/-- Representative-choice homotopies fix every point of the exactly normalized neutral slice. -/
theorem qLoopComponentProductChoiceHomotopy_identity
    (r : E.DiscreteKZero → Path E.kBasepoint E.kBasepoint)
    (hr : ∀ a, E.loopKZeroLabel (r a) = a) (t : I) (z : E.QLoopIdentityComponent) :
    E.qLoopComponentProductChoiceHomotopy r hr (t, (E.discreteKZeroIdentity, z)) = z.val :=
  normalizedLoopComponentProductHomotopy_zero _ _ _ _

end CategoryTheory.ExactCategory.ExactStructure

namespace CategoryTheory.ExactCategory.ExactFunctor
open Topology CategoryTheory
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- The original K₀ map on the discrete label copies. -/
def discreteKZeroMap (F : ExactFunctor EC ED) (a : EC.DiscreteKZero) : ED.DiscreteKZero :=
  WithTopology.toTopology ⊥ (F.KMap 0 a.ofTopology)

/-- The actual original normalized-Q loop map preserves the unchanged component labels. -/
theorem loopKZeroLabel_naturality (F : ExactFunctor EC ED)
    (γ : Path EC.kBasepoint EC.kBasepoint) :
    ED.loopKZeroLabel
      (basedLoopMap (classifyingSpaceMap F.normalizedQ).hom F.normalizedQ_map_point γ) =
      F.discreteKZeroMap (EC.loopKZeroLabel γ) := by
  apply WithTopology.ext
  exact (F.loopComponentsKZeroEquiv_naturality γ).symm

/-- The transported chosen representative has an actual path to the target chosen representative. -/
def qLoopRepresentativeNaturalityPath (F : ExactFunctor EC ED) (a : EC.DiscreteKZero) :
    Path (basedLoopMap (classifyingSpaceMap F.normalizedQ).hom F.normalizedQ_map_point
      (EC.qLoopRepresentative a)) (ED.qLoopRepresentative (F.discreteKZeroMap a)) := by
  apply Joined.somePath
  apply (ED.loopKZeroLabel_eq_iff _ _).mp
  rw [F.loopKZeroLabel_naturality, EC.qLoopRepresentative_label, ED.qLoopRepresentative_label]

/-- The normalized actual products are natural in the ordinary homotopy category. -/
theorem qLoopComponentProductEquiv_naturality (F : ExactFunctor EC ED) :
    ((basedLoopMap (classifyingSpaceMap F.normalizedQ).hom F.normalizedQ_map_point).comp
      EC.qLoopComponentProductEquiv.toFun).Homotopic
        (ED.qLoopComponentProductEquiv.toFun.comp
          (loopComponentProductChange (classifyingSpaceMap F.normalizedQ).hom
            F.normalizedQ_map_point F.discreteKZeroMap)) :=
  normalizedLoopComponentProductMap_naturality
    (classifyingSpaceMap F.normalizedQ).hom F.normalizedQ_map_point F.discreteKZeroMap
    EC.discreteKZeroIdentity ED.discreteKZeroIdentity EC.qLoopRepresentative ED.qLoopRepresentative
    EC.qLoopRepresentative_identity ED.qLoopRepresentative_identity
    F.qLoopRepresentativeNaturalityPath

end CategoryTheory.ExactCategory.ExactFunctor
