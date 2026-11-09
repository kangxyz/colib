/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassConnectivity
public import Colib.Topology.Prespectrum.ConeFiberConnectivity
public import Colib.Topology.Prespectrum.StableConnectivity

/-!
# Genuine cone excision for all actual finite section Bass iterates

For an unchanged arrow from stage i over R to stage j over S, the proved all-point connectivity
bounds and original point HEP give finite cone excision at level n+max(i,j)+2 with range 2*n+2.
The genuine eventual signed-colimit criterion then proves stable excision, including arbitrary
negative degrees. The source and the complete original cone-cylinder path remain unchanged.
No growth or excision assumption remains, and low levels below the cutoff are not constrained.
-/
/-! Implementation provenance:
`Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConeExcision.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section

noncomputable section
open Topology TopCat
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable (i j : ℕ) (R S : CommRingCat.{u})
  (f : (boundedAboveFlatAffineSectionBassDiagram i).obj R ⟶
    (boundedAboveFlatAffineSectionBassDiagram j).obj S)

/-- Original maps between any two actual finite stages have genuine finite cone excision. -/
theorem boundedAboveFlatAffineSectionBass_map_coneFiber_isHomotopyConnectedMap (n : ℕ) :
    IsHomotopyConnectedMap ((mappingConeFiberComparison f).map (n + max i j + 2))
      (2 * n + 2) := by
  have hX (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj R).space (n + max i j + 2))
      (k : ℕ) (hk : k < n + 2) : Subsingleton (HomotopyGroup.Pi k
        (((boundedAboveFlatAffineSectionBassDiagram i).obj R).space (n + max i j + 2)) x) :=
    boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le
      i R (n + max i j + 2) (by omega) k (by omega) x
  have hY (y : ((boundedAboveFlatAffineSectionBassDiagram j).obj S).space (n + max i j + 2))
      (k : ℕ) (hk : k < n + 2) : Subsingleton (HomotopyGroup.Pi k
        (((boundedAboveFlatAffineSectionBassDiagram j).obj S).space (n + max i j + 2)) y) :=
    boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le
      j S (n + max i j + 2) (by omega) k (by omega) y
  let := pathConnectedSpace_of_subsingleton_pi_zero
    (((boundedAboveFlatAffineSectionBassDiagram j).obj S).point (n + max i j + 2))
    (hY _ 0 (by omega))
  apply mappingConeFiberComparison_level_isHomotopyConnectedMap f (n + max i j + 2)
    (boundedAboveFlatAffineSectionBassDiagram_point_homotopyExtensionProperty i R _)
    (boundedAboveFlatAffineSectionBassDiagram_point_homotopyExtensionProperty j S _)
    (n + 1) (n + 2) (2 * n + 2) (by omega)
  · exact isHomotopyConnectedMap_of_vanishing (f.map (n + max i j + 2))
      (((boundedAboveFlatAffineSectionBassDiagram i).obj R).point (n + max i j + 2)) (n + 1)
      (fun x k hk ↦ hX x k (by omega)) (fun y k hk ↦ hY y k (by omega))
  · exact isHomotopyConnectedMap_const_of_vanishing
      (((boundedAboveFlatAffineSectionBassDiagram i).obj R).point (n + max i j + 2)) (n + 2) hX

/-- Every original arrow between actual finite Bass stages has stable cone-to-fiber excision. -/
theorem boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence :
    IsStableEquivalence (mappingConeFiberComparison f) := by
  apply isStableEquivalence_of_eventually_linearConnectivity (mappingConeFiberComparison f)
    (max i j + 1) (2 * max i j)
  intro n hn
  have h := boundedAboveFlatAffineSectionBass_map_coneFiber_isHomotopyConnectedMap
    i j R S f (n - (max i j + 1))
  rw [show n - (max i j + 1) + max i j + 2 = n + 1 by omega,
    show 2 * (n - (max i j + 1)) + 2 = 2 * n - 2 * max i j by omega] at h
  exact h

/-- Every unchanged coefficient arrow at each actual finite Bass stage has stable cone excision.
-/
theorem boundedAboveFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence
    (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsStableEquivalence
      (mappingConeFiberComparison ((boundedAboveFlatAffineSectionBassDiagram i).map f)) :=
  boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence
    i i R S ((boundedAboveFlatAffineSectionBassDiagram i).map f)

/-- The actual iterated Laurent seed between consecutive stages also has genuine stable excision.
-/
theorem boundedAboveFlatAffineSectionBass_transition_coneFiber_isStableEquivalence
    (i : ℕ) (R : CommRingCat.{u}) :
    IsStableEquivalence
      (mappingConeFiberComparison ((boundedAboveFlatAffineSectionBassTransition i).app R)) :=
  boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence
    i (i + 1) R R ((boundedAboveFlatAffineSectionBassTransition i).app R)


attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConeExcision.lean:31"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  boundedAboveFlatAffineSectionBass_map_coneFiber_isHomotopyConnectedMap

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConeExcision.lean:58"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConeExcision.lean:71"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  boundedAboveFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConeExcision.lean:80"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  boundedAboveFlatAffineSectionBass_transition_coneFiber_isStableEquivalence

attribute [colib_tag "COL-0375"]
  boundedAboveFlatAffineSectionBass_map_coneFiber_isHomotopyConnectedMap
  boundedAboveFlatAffineSectionBass_map_coneFiber_isStableEquivalence
  boundedAboveFlatAffineSectionBass_coefficient_coneFiber_isStableEquivalence
  boundedAboveFlatAffineSectionBass_transition_coneFiber_isStableEquivalence

end AlgebraicGeometry.Scheme.Modules
