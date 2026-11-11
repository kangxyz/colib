module
import Colib.KTheory.Bass.ConeDiagramNull
import Colib.Topology.Prespectrum.DiagramNullTransport
open CategoryTheory Topology Topology.LoopPrespectrum KTheory.Bass
universe u v w
noncomputable section
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    {F G K : C ⥤ LoopPrespectrum.{w}} (a : F ⟶ G) (b : G ⟶ K)
example : ConeTrack.map Q (a ≫ b) = ConeTrack.map Q a ≫ ConeTrack.map Q b :=
  ConeTrack.map_comp Q a b
example (N : DiagramNullHomotopy a b) :
    DiagramNullHomotopy (ConeTrack.map Q a) (ConeTrack.map Q b) := ConeTrack.diagramNull Q N
example (N : DiagramNullHomotopy a b) (X : C) (r : unitInterval) :
    ((ConeTrack.diagramNull Q N).homotopy X).at r =
      (ConeTrack.map Q (diagramHomotopyAt (η := a ≫ b) (θ := diagramZeroMap F K)
        N.homotopy N.naturality r)).app X := ConeTrack.diagramNull_at Q N X r

variable {F' G' K' : C ⥤ LoopPrespectrum.{w}} {a' : F' ⟶ G'} {b' : G' ⟶ K'}
    (H : DiagramNullHomotopy a b)
    (eF : F' ≅ F) (eG : G' ≅ G) (eK : K' ≅ K)
    (ha : a' ≫ eG.hom = eF.hom ≫ a) (hb : b' ≫ eK.hom = eG.hom ≫ b)
example : DiagramNullHomotopy a' b' := H.transport eF eG eK ha hb
example (X : C) : mappingCone (a'.app X) ≅ mappingCone (a.app X) :=
  DiagramNullHomotopy.coneTransportIso eF eG ha X
