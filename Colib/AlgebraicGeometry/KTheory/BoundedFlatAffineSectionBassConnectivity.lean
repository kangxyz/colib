/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassPointHEP
public import Colib.KTheory.Bass.StrictDiagramVanishing
public import Colib.KTheory.Waldhausen.Iterated.FiniteConnectivity

/-!
# Actual finite connectivity growth at every section Bass iterate

The proved original S-level growth and literal point HEP discharge the seed assumptions.
The actual reduced pushout, cone and parameter-loop proofs give offset i at Bass stage i:
at original level n+i+2 all homotopy sets below n+2 vanish at every point. Point maps have
connectivity n+2 and original maps between such stages have connectivity n+1. The cutoff
is explicit; no low-level component assertion or eventual-growth premise is introduced.
-/
/-! Implementation provenance:
`Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConnectivity.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section

noncomputable section
open Topology TopCat
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Every actual finite Bass iterate has the proved one-degree-per-step growth offset. -/
theorem boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at
    (i : ℕ) (R : CommRingCat.{u}) (n k : ℕ) (hk : k < n + 2)
    (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj R).space (n + i + 2)) :
    Subsingleton (HomotopyGroup.Pi k
      (((boundedAboveFlatAffineSectionBassDiagram i).obj R).space (n + i + 2)) x) := by
  have hπ := KTheory.Bass.strictDiagramIterate_homotopyGroup_subsingleton
    CommRingCat.PolynomialLaurent.laurentSquareFunctor i
    boundedAboveFlatAffineSectionPrespectrumFunctor
    boundedAboveFlatAffineSectionPrespectrum_point_homotopyExtensionProperty 0
    (fun S m j hj y ↦ Waldhausen.IteratedS.prespectrum_positiveLevel_homotopyGroup_subsingleton_at
      (boundedAboveFlatAffineSectionModel S) (m + 1) j (by omega) y) R n k hk
  rw [Nat.zero_add] at hπ
  exact hπ x

/-- The same genuine bound in an arbitrary original level above the explicit stage cutoff. -/
theorem boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le
    (i : ℕ) (R : CommRingCat.{u}) (m : ℕ) (hm : i + 2 ≤ m)
    (k : ℕ) (hk : k + i < m)
    (x : ((boundedAboveFlatAffineSectionBassDiagram i).obj R).space m) :
    Subsingleton (HomotopyGroup.Pi k
      (((boundedAboveFlatAffineSectionBassDiagram i).obj R).space m) x) := by
  let n := m - (i + 2)
  have he : n + i + 2 = m := by dsimp [n]; omega
  have hπ := boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at i R n k
    (by dsimp [n]; omega)
  rw [he] at hπ
  exact hπ x

/-- The original stage-to-point map has the sharper finite bound above its explicit cutoff. -/
theorem boundedAboveFlatAffineSectionBassDiagram_toPoint_isHomotopyConnectedMap
    (i : ℕ) (R : CommRingCat.{u}) (n : ℕ) :
    IsHomotopyConnectedMap (ContinuousMap.const
      (((boundedAboveFlatAffineSectionBassDiagram i).obj R).space (n + i + 2))
      (PUnit.unit : PUnit.{u + 2})) (n + 2) :=
  isHomotopyConnectedMap_const_of_vanishing
    (((boundedAboveFlatAffineSectionBassDiagram i).obj R).point (n + i + 2)) (n + 2)
    (fun x k hk ↦ boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at
      i R n k hk x)

/-- Any original map between stage-i models has a proved finite bound at the unchanged level. -/
theorem boundedAboveFlatAffineSectionBassDiagram_map_isHomotopyConnectedMap
    (i : ℕ) (R S : CommRingCat.{u})
    (f : (boundedAboveFlatAffineSectionBassDiagram i).obj R ⟶
      (boundedAboveFlatAffineSectionBassDiagram i).obj S) (n : ℕ) :
    IsHomotopyConnectedMap (f.map (n + i + 2)) (n + 1) := by
  let := pathConnectedSpace_of_subsingleton_pi_zero
    (((boundedAboveFlatAffineSectionBassDiagram i).obj S).point (n + i + 2))
    (boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at i S n 0 (by omega) _)
  exact isHomotopyConnectedMap_of_vanishing (f.map (n + i + 2))
    (((boundedAboveFlatAffineSectionBassDiagram i).obj R).point (n + i + 2)) (n + 1)
    (fun x k hk ↦ boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at
      i R n k (by omega) x)
    (fun y k hk ↦ boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at
      i S n k (by omega) y)

/-- The original iterated seed transition itself has increasing finite connectivity; source
and successor target bounds are both discharged at the displayed higher cutoff. -/
theorem boundedAboveFlatAffineSectionBassTransition_isHomotopyConnectedMap
    (i : ℕ) (R : CommRingCat.{u}) (n : ℕ) :
    IsHomotopyConnectedMap
      (((boundedAboveFlatAffineSectionBassTransition i).app R).map (n + i + 3)) (n + 1) := by
  let := pathConnectedSpace_of_subsingleton_pi_zero
    (((boundedAboveFlatAffineSectionBassDiagram (i + 1)).obj R).point (n + i + 3))
    (boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le
      (i + 1) R (n + i + 3) (by omega) 0 (by omega) _)
  exact isHomotopyConnectedMap_of_vanishing
    (((boundedAboveFlatAffineSectionBassTransition i).app R).map (n + i + 3))
    (((boundedAboveFlatAffineSectionBassDiagram i).obj R).point (n + i + 3)) (n + 1)
    (fun x k hk ↦ boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le
      i R (n + i + 3) (by omega) k (by omega) x)
    (fun y k hk ↦ boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le
      (i + 1) R (n + i + 3) (by omega) k (by omega) y)


attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConnectivity.lean:28"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConnectivity.lean:42"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConnectivity.lean:56"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  boundedAboveFlatAffineSectionBassDiagram_toPoint_isHomotopyConnectedMap

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConnectivity.lean:67"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  boundedAboveFlatAffineSectionBassDiagram_map_isHomotopyConnectedMap

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassConnectivity.lean:84"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  boundedAboveFlatAffineSectionBassTransition_isHomotopyConnectedMap

attribute [colib_tag "COL-0375"]
  boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_at
  boundedAboveFlatAffineSectionBassDiagram_homotopyGroup_subsingleton_of_le
  boundedAboveFlatAffineSectionBassDiagram_toPoint_isHomotopyConnectedMap
  boundedAboveFlatAffineSectionBassDiagram_map_isHomotopyConnectedMap
  boundedAboveFlatAffineSectionBassTransition_isHomotopyConnectedMap

end AlgebraicGeometry.Scheme.Modules
