/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Prespectrum.PushoutInterchangeIso
noncomputable section
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout.SpanGrid
variable (G : SpanGrid.{u})

example : G.transpose.transpose = G := transpose_transpose G
example : G.iterated ⟶ G.transpose.iterated := G.interchange
example : G.interchange ≫ G.transpose.interchange = 𝟙 G.iterated :=
  interchange_comp_transpose G
example : G.iterated ≅ G.transpose.iterated := G.interchangeIso

example (n : ℕ) (r : unitInterval) (s : unitInterval) (x :
  (G.obj 0 0).space n) :
    G.interchange.map n
      (cylinder G.rowLeft G.rowRight n (r, cylinder (G.horizontalLeft 0) (G.horizontalRight 0) n
        (s, x))) =
        cylinder G.transpose.rowLeft G.transpose.rowRight n (s, cylinder (G.verticalLeft 0)
          (G.verticalRight 0) n (r, x)) :=
  interchange_cylinder_cylinder G n r s x

example (n : ℕ) (x : G.iterated.space n) (t : unitInterval) :
    G.interchange.map (n + 1) (G.iterated.structureMap n x t) =
      G.transpose.iterated.structureMap n (G.interchange.map n x) t :=
  interchange_structure G n x t

example {G G' : SpanGrid.{u}} (h : Hom G G') :
    h.iteratedMap ≫ G'.interchange = G.interchange ≫ h.transpose.iteratedMap :=
  Hom.interchange_naturality h

end Topology.LoopPrespectrum.HomotopyPushout.SpanGrid
end
