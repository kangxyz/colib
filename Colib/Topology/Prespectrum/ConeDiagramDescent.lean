/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.ConeDiagram


/-!
# Original pointwise cone diagrams and prescribed natural descents

The existing arrow-diagram interchange forms the pointwise original mapping cones. A specified
coefficient-natural whole null track makes the actual quotient descents into a natural
transformation, retaining the original coefficient arrows and every cylinder value.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace Topology.LoopPrespectrum
variable {C : Type u} [Category.{v} C] {F G K : C ⥤ LoopPrespectrum.{w}} (a : F ⟶ G)

/-- The original coefficient maps are the unchanged strict cone maps. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeDiagram.lean:30"
  "adaptation" "Original pointwise cone arrows and complete natural quotient descent"]
theorem mappingConeDiagram_map {X Y : C} (f : X ⟶ Y) :
    (mappingConeDiagram a).map f =
      mappingConeMap (Arrow.homMk (F.map f) (G.map f) (a.naturality f)) := rfl

/-- The actual quotient descents form a transformation when their entire null tracks are natural. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeDiagram.lean:35"
  "adaptation" "Original pointwise cone arrows and complete natural quotient descent"]
def mappingConeDescTransformation (b : G ⟶ K)
    (N : ∀ X, Homotopy (a.app X ≫ b.app X) (zeroHom (F.obj X) (K.obj X)))
    (hN : ∀ {X Y} (f : X ⟶ Y) n r x,
      (K.map f).map n ((N X).level n (r, x)) =
        (N Y).level n (r, (F.map f).map n x)) : mappingConeDiagram a ⟶ K where
  app X := mappingConeDesc (a.app X) (b.app X) (N X)
  naturality X Y f := mappingConeDesc_naturality
    (Arrow.homMk (f := Arrow.mk (a.app X)) (g := Arrow.mk (a.app Y))
      (F.map f) (G.map f) (a.naturality f)) (b.app X) (b.app Y) (K.map f)
    (N X) (N Y) (b.naturality f) (hN f)

end Topology.LoopPrespectrum

