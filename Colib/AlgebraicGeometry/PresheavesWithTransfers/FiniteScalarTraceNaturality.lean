/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.BaseChange.ScalarTraceNaturality
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.FiniteScalarTrace

/-!
# Flat trace naturality on the unchanged original presheaf

Both equalities are the action of the proved equality between the actual
whole-support correspondences. The coefficient universe is arbitrary. Neither
homotopy invariance nor sheafification is used.

Adapted from `Motivic/Transfers/Presheaf/FiniteScalarTrace.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)

/-- An actual flat Cartesian square commutes with transfer on original sections. -/
theorem finiteFlatTrace_cartesian {X Y U V : SmoothSite (Spec (.of k))}
    (p : Y ⟶ X) [IsFinite p.left] [Flat p.left]
    (q : V ⟶ U) [IsFinite q.left] [Flat q.left]
    (j : U ⟶ X) [Flat j.left] (i : V ⟶ Y)
    (sq : IsPullback q.left i.left j.left p.left) :
    transfer P ((Cor.graphFunctor k).map i) ≫ transfer P (Cor.finiteFlatTrace q) =
      transfer P (Cor.finiteFlatTrace p) ≫ transfer P ((Cor.graphFunctor k).map j) := by
  exact (transfer_comp P (Cor.finiteFlatTrace q) ((Cor.graphFunctor k).map i)).symm.trans
    ((congrArg (transfer P) (Cor.finiteFlatTrace_cartesian p q j i sq)).trans
      (transfer_comp P ((Cor.graphFunctor k).map j) (Cor.finiteFlatTrace p)))

variable {E : Type u} [Field E] [Algebra k E]
  [Module.Finite k E] [Algebra.IsSeparable k E]

/-- The actual scalar trace commutes with each flat original restriction. -/
theorem finiteScalarTrace_naturality {U X : SmoothSite (Spec (.of k))}
    (j : U ⟶ X) [Flat j.left] :
    transfer P ((Cor.graphFunctor k).map (SmoothSite.finiteScalarMap (E := E) j)) ≫
        transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) U)) =
      transfer P (Cor.finiteFlatTrace (SmoothSite.finiteScalarProjection (E := E) X)) ≫
        transfer P ((Cor.graphFunctor k).map j) := by
  let q := SmoothSite.finiteScalarProjection (E := E) U
  let p := SmoothSite.finiteScalarProjection (E := E) X
  let i := SmoothSite.finiteScalarMap (E := E) j
  exact (transfer_comp P (Cor.finiteFlatTrace q) ((Cor.graphFunctor k).map i)).symm.trans
    ((congrArg (transfer P) (Cor.finiteScalarTrace_naturality (E := E) j)).trans
      (transfer_comp P ((Cor.graphFunctor k).map j) (Cor.finiteFlatTrace p)))

end AlgebraicGeometry.PresheafWithTransfers
