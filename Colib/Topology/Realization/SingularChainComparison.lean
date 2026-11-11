/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# The actual simplicial-to-singular chain comparison

The comparison is the chain map of the unit of `sSetTopAdj`. It sends each
simplicial simplex to its characteristic singular simplex, with the original
ordering of faces. Its naturality square retains the realized original map.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicTopology
open scoped Simplicial

universe w v u

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

/-- The unit-induced map from simplicial chains to singular chains of the realization. -/
noncomputable def realizationChainComparison (X : SSet.{w}) (R : C) :
    X.chainComplex R ⟶
      ((singularChainComplexFunctor C).obj R).obj (SSet.toTop.obj X) :=
  chainComplexMap (sSetTopAdj.unit.app X) R

/-- The comparison sends a generator to the singular simplex of the actual adjunction unit. -/
@[reassoc (attr := simp)]
lemma ι_realizationChainComparison_f (X : SSet.{w}) (R : C) {n : ℕ}
    (x : X _⦋n⦌) :
    X.ιChainComplex x ≫ (realizationChainComparison X R).f n =
      (TopCat.toSSet.obj (SSet.toTop.obj X)).ιChainComplex
        ((sSetTopAdj.unit.app X).app _ x) :=
  ι_chainComplexMap_f X _ (sSetTopAdj.unit.app X) R x

/-- Naturality retains the chain map of the original topological realization. -/
@[reassoc]
lemma realizationChainComparison_naturality {X Y : SSet.{w}} (f : X ⟶ Y) (R : C) :
    chainComplexMap f R ≫ realizationChainComparison Y R =
      realizationChainComparison X R ≫
        ((singularChainComplexFunctor C).obj R).map (SSet.toTop.map f) := by
  change ((chainComplexFunctor C).obj R).map f ≫
      ((chainComplexFunctor C).obj R).map (sSetTopAdj.unit.app Y) =
    ((chainComplexFunctor C).obj R).map (sSetTopAdj.unit.app X) ≫
      ((chainComplexFunctor C).obj R).map (TopCat.toSSet.map (SSet.toTop.map f))
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact ((chainComplexFunctor C).obj R).congr_map (sSetTopAdj.unit.naturality f)

variable [CategoryWithHomology C]

/-- Two quasi-isomorphic unit comparisons transfer singular homology invariance
to the original simplicial chain map. -/
lemma quasiIso_chainComplexMap_of_realizationChainComparison
    {X Y : SSet.{w}} (f : X ⟶ Y) (R : C)
    [QuasiIso (realizationChainComparison X R)]
    [QuasiIso (realizationChainComparison Y R)]
    [QuasiIso (((singularChainComplexFunctor C).obj R).map (SSet.toTop.map f))] :
    QuasiIso (chainComplexMap f R) := by
  have h : QuasiIso (chainComplexMap f R ≫ realizationChainComparison Y R) := by
    rw [realizationChainComparison_naturality]
    infer_instance
  exact quasiIso_of_comp_right _ (realizationChainComparison Y R)

end SSet
