/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphSingleton

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u v

variable {k : Type u} [Field k]

example (F : (Cor k)ᵒᵖ ⥤ Type v) {X Y : SmoothSite (Spec (.of k))} (q : Y ⟶ X)
    (hF : Presieve.IsSheafFor ((Cor.graphFunctor k).op ⋙ F) (Presieve.singleton q)) :
    Presieve.IsSheafFor F (Presieve.singleton ((Cor.graphFunctor k).map q)) :=
  PresheafWithTransfers.isSheafFor_graph_singleton_of_restriction F q hF

example (F : (Cor k)ᵒᵖ ⥤ Type v) (X : SmoothSite (Spec (.of k))) :
    Presieve.IsSheafFor F (Presieve.singleton ((Cor.graphFunctor k).map (𝟙 X))) := by
  rw [CategoryTheory.Functor.map_id]
  exact Presieve.isSheafFor_singleton_iso F
