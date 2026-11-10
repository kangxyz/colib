module

import Colib.RingTheory.AdjoinRoot.ResidueField

noncomputable section

open Polynomial IsLocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A] (p : A[X])
  [IsLocalRing (AdjoinRoot p)] (hirr : Irreducible (p.map (residue A)))

example : ResidueField (AdjoinRoot p) ≃+* AdjoinRoot (p.map (residue A)) :=
  AdjoinRoot.residueFieldEquivAdjoinRoot p hirr

example (q : A[X]) :
    AdjoinRoot.residueFieldEquivAdjoinRoot p hirr
        (residue (AdjoinRoot p) (AdjoinRoot.mk p q)) =
      AdjoinRoot.mk (p.map (residue A)) (q.map (residue A)) :=
  AdjoinRoot.residueFieldEquivAdjoinRoot_residue_mk p hirr q
