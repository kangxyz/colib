module

public import Colib.Topology.CWComplex.CellNeighborhood

open Set Topology Topology.CWComplex
open scoped Topology unitInterval

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C]

example (n : ℕ) (i : RelCWComplex.cell C n) :
    IsOpen (cellNeighborhoodSet C n i) :=
  isOpen_cellNeighborhoodSet C n i

example (n : ℕ) (i : RelCWComplex.cell C n) (x : CellNeighborhood C n i) :
    ∃ H : (cellNeighborhoodToComplex C n i).Homotopy
        (ContinuousMap.const (CellNeighborhood C n i) (cellNeighborhoodToComplex C n i x)),
      ∀ (y : CellNeighborhood C n i) (t : I), (t : ℝ) ≤ 1 / 2 →
        H (t, y) = cellNeighborhoodToComplex C n i y :=
  ⟨cellNeighborhoodAmbientContraction C n i x,
    cellNeighborhoodAmbientContraction_stationary C n i x⟩

example (x : C) :
    ∃ (n : ℕ) (i : RelCWComplex.cell C n) (y : CellNeighborhood C n i),
      cellNeighborhoodToComplex C n i y = x := by
  obtain ⟨n, i, y, hy⟩ := exists_cellNeighborhood C x
  exact ⟨n, i, y, Subtype.ext hy⟩

#print axioms cellNeighborhoodAmbientContraction
#print axioms exists_cellNeighborhood
