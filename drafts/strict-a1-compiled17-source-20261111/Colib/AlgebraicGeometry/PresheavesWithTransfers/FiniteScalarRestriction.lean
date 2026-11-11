/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.GraphRestriction
public import Colib.AlgebraicGeometry.Sites.Smooth.ScalarExtension.Finite.Basic

/-!
# Naturality of the actual scalar restriction

This is the projection-square consequence of the real scalar base change.
It requires neither trace naturality nor flatness of the original restriction.
Extracted from motivic's `FiniteScalarDescent.finiteScalarRestriction_naturality`;
the factorization-family descent statements are not asserted in this leaf.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)
variable {E : Type u} [Field E] [Algebra k E]
  [Module.Finite k E] [Algebra.IsSeparable k E]

/-- Original scalar restriction is natural for every original scheme map. -/
theorem finiteScalarRestriction_naturality {V X : SmoothSite (Spec (.of k))}
    (j : V ⟶ X) :
    transfer P ((Cor.graphFunctor k).map j) ≫
        transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarProjection (E := E) V)) =
      transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarProjection (E := E) X)) ≫
        transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) j)) := by
  have h : SmoothSite.finiteScalarMap (E := E) j ≫
      SmoothSite.finiteScalarProjection (E := E) X =
      SmoothSite.finiteScalarProjection (E := E) V ≫ j := by
    apply MorphismProperty.Over.Hom.ext
    exact (SmoothSite.finiteScalarMap_isPullback (E := E) j).w.symm
  have he := congrArg (fun f => transfer P ((Cor.graphFunctor k).map f)) h
  simpa only [Functor.map_comp, transfer_comp] using he.symm

end AlgebraicGeometry.PresheafWithTransfers
