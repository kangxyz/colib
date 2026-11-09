/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.TelescopeStableEquivalence

/-!
# The canonical stable-group colimit comparison for the original telescope

The original stage inclusions induce a canonical map from the categorical
filtered colimit of stage stable groups to the unchanged stable group of the
actual reduced telescope. For levelwise T1 stages this canonical map is an
isomorphism, naturally for strict maps of the original sequential diagrams.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))

/-- The original stable groups of the stages, with their original connecting maps. -/
def stageStableDiagram (d : ℤ) : ℕ ⥤ AddCommGrpCat.{u} :=
  Functor.ofSequence f ⋙ stableHomotopyFunctor d

/-- The original telescope inclusions form a cocone on the stage stable groups. -/
def stableCocone (d : ℤ) : Cocone (stageStableDiagram E f d) where
  pt := stableHomotopyGroup (prespectrum E f) d
  ι :=
    { app := fun i ↦ (stableHomotopyFunctor d).map (inclusion E f i)
      naturality := fun i j h ↦ by
        exact (inclusion_transition_stableMap E f (leOfHom h) d).symm.trans
          (Category.comp_id _).symm }

/-- The canonical map from the actual stage colimit into the original telescope stable group. -/
def stableColimitComparison (d : ℤ) :
    colimit (stageStableDiagram E f d) ⟶ stableHomotopyGroup (prespectrum E f) d :=
  colimit.desc _ (stableCocone E f d)

@[reassoc (attr := simp)] theorem stableColimitComparison_ι (d : ℤ) (i : ℕ) :
    colimit.ι (stageStableDiagram E f d) i ≫ stableColimitComparison E f d =
      (stableHomotopyFunctor d).map (inclusion E f i) :=
  colimit.ι_desc _ _

variable [∀ i k, T1Space ((E i).space k)]

/-- Finite representatives and eventual equality prove that the canonical comparison is an iso. -/
instance stableColimitComparison_isIso (d : ℤ) : IsIso (stableColimitComparison E f d) := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y hxy
    obtain ⟨i, x, rfl⟩ := Concrete.colimit_exists_rep (stageStableDiagram E f d) x
    obtain ⟨j, y, rfl⟩ := Concrete.colimit_exists_rep (stageStableDiagram E f d) y
    have hxy' := (ConcreteCategory.congr_hom (stableColimitComparison_ι E f d i) x).symm.trans
      (hxy.trans (ConcreteCategory.congr_hom (stableColimitComparison_ι E f d j) y))
    obtain ⟨N, hi, hj, hN⟩ := exists_eventual_stable_eq E f d x y hxy'
    exact (colimit.w_apply (stageStableDiagram E f d) (homOfLE hi) x).symm.trans
      ((congrArg (colimit.ι (stageStableDiagram E f d) N) hN).trans
        (colimit.w_apply (stageStableDiagram E f d) (homOfLE hj) y))
  · intro y
    obtain ⟨i, x, rfl⟩ := exists_stable_representative E f d y
    exact ⟨colimit.ι (stageStableDiagram E f d) i x,
      ConcreteCategory.congr_hom (stableColimitComparison_ι E f d i) x⟩

/-- The canonical filtered-colimit isomorphism onto the unchanged original stable group. -/
@[colib_tag "COL-0350"]
def stableColimitIso (d : ℤ) :
    colimit (stageStableDiagram E f d) ≅ stableHomotopyGroup (prespectrum E f) d :=
  asIso (stableColimitComparison E f d)

@[simp] theorem stableColimitIso_hom (d : ℤ) :
    (stableColimitIso E f d).hom = stableColimitComparison E f d := rfl

@[reassoc] theorem stableColimitIso_ι_hom (d : ℤ) (i : ℕ) :
    colimit.ι (stageStableDiagram E f d) i ≫ (stableColimitIso E f d).hom =
      (stableHomotopyFunctor d).map (inclusion E f i) := stableColimitComparison_ι E f d i

end Topology.LoopPrespectrum.Telescope

namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  (E' : ℕ → LoopPrespectrum.{u}) (f' : ∀ i, E' i ⟶ E' (i + 1))
  (a : ∀ i, E i ⟶ E' i) (ha : ∀ i, a i ≫ f' i = f i ≫ a (i + 1))

/-- A strict original diagram map induces the corresponding map of stage stable diagrams. -/
def stageStableDiagramMap (d : ℤ) : stageStableDiagram E f d ⟶ stageStableDiagram E' f' d where
  app i := (stableHomotopyFunctor d).map (a i)
  naturality i j h := by
    change (stableHomotopyFunctor d).map (transition E f i j (leOfHom h)) ≫
      (stableHomotopyFunctor d).map (a j) =
        (stableHomotopyFunctor d).map (a i) ≫
          (stableHomotopyFunctor d).map (transition E' f' i j (leOfHom h))
    have hn := congrArg ((stableHomotopyFunctor d).map)
      (transition_naturality E f E' f' a ha i j (leOfHom h))
    simpa only [Functor.map_comp] using hn

/-- The canonical comparison is natural for the original strict diagram maps. -/
@[reassoc] theorem stableColimitComparison_naturality (d : ℤ) :
    colimMap (stageStableDiagramMap E f E' f' a ha d) ≫ stableColimitComparison E' f' d =
      stableColimitComparison E f d ≫ (stableHomotopyFunctor d).map (map E f E' f' a ha) := by
  apply colimit.hom_ext
  intro i
  erw [ι_colimMap_assoc, stableColimitComparison_ι, stableColimitComparison_ι_assoc]
  change (stableHomotopyFunctor d).map (a i) ≫
    (stableHomotopyFunctor d).map (inclusion E' f' i) =
      (stableHomotopyFunctor d).map (inclusion E f i) ≫
        (stableHomotopyFunctor d).map (map E f E' f' a ha)
  have h := congrArg ((stableHomotopyFunctor d).map) (inclusion_map E f E' f' a ha i)
  simpa only [Functor.map_comp] using h.symm

variable [∀ i k, T1Space ((E i).space k)] [∀ i k, T1Space ((E' i).space k)]

/-- The proved comparison isomorphisms retain the same original-map naturality square. -/
@[reassoc] theorem stableColimitIso_naturality (d : ℤ) :
    colimMap (stageStableDiagramMap E f E' f' a ha d) ≫ (stableColimitIso E' f' d).hom =
      (stableColimitIso E f d).hom ≫ (stableHomotopyFunctor d).map (map E f E' f' a ha) :=
  stableColimitComparison_naturality E f E' f' a ha d

end Topology.LoopPrespectrum.Telescope
