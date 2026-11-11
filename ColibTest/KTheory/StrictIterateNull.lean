module
import Colib.KTheory.Bass.StrictDiagramIterateNullTimeSlice
open CategoryTheory Topology Topology.LoopPrespectrum KTheory.Bass
universe u v w
noncomputable section
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    {F G K : C ⥤ LoopPrespectrum.{w}} {a : F ⟶ G} {b : G ⟶ K}
example (i : ℕ) : IsIso (strictDiagramSuccessorMap Q F i) := inferInstance
example (N : DiagramNullHomotopy a b) (i : ℕ) :
    DiagramNullHomotopy ((strictDiagramIterate Q i).map a)
      ((strictDiagramIterate Q i).map b) := strictDiagramIterateNull Q N i
example (N : DiagramNullHomotopy a b) : strictDiagramIterateNull Q N 0 = N :=
  strictDiagramIterateNull_zero Q N
example (i : ℕ) :
    (strictDiagramIterate Q (i + 1)).map a ≫ strictDiagramSuccessorMap Q G i =
      strictDiagramSuccessorMap Q F i ≫
        (strictDiagramFunctor Q).map ((strictDiagramIterate Q i).map a) :=
  strictDiagramSuccessorMap_naturality Q a i
