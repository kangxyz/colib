/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.SingularChainComparison
public import Colib.Topology.Realization.SimplexConnectivity
public import Colib.Topology.Homotopy.ContractibleMap
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Terminal

/-!
# The unit chain comparison on standard simplices

The simplicial augmentation is a chain homotopy equivalence by the native extra
degeneracy. The realized augmentation is a homotopy equivalence by contractibility
of the native topological simplex. Naturality with the zero-dimensional simplex
then proves that the actual adjunction unit is a quasi-isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicTopology
open scoped Simplicial

universe w v u

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]

private def extraDegeneracyChainHomotopyEquiv (X : SSet.Augmented.{w})
    (ed : SimplicialObject.Augmented.ExtraDegeneracy X) (R : C) :
    _root_.HomotopyEquiv (SSet.chainComplex X.left R)
      (SSet.chainComplex ((SimplicialObject.const (Type w)).obj X.right) R) where
  hom := chainComplexMap X.hom R
  inv := chainComplexMap ed.section_ R
  homotopyHomInvId := by
    change _root_.Homotopy
      (((chainComplexFunctor C).obj R).map X.hom ≫
        ((chainComplexFunctor C).obj R).map ed.section_)
      (𝟙 (((chainComplexFunctor C).obj R).obj X.left))
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_id]
    exact ed.homotopy.sSetChainComplexMap R
  homotopyInvHomId := _root_.Homotopy.ofEq (by
    rw [← CategoryTheory.Functor.map_comp, ed.section_comp_hom]
    exact ((chainComplexFunctor C).obj R).map_id _)

/-- An actual topological homotopy equivalence induces a quasi-isomorphism on
Mathlib's singular chains, with the original forward map. -/
lemma quasiIso_singular_of_homotopyEquiv [CategoryWithHomology C]
    {X Y : TopCat.{w}} (e : ContinuousMap.HomotopyEquiv X Y) (R : C) :
    QuasiIso (((singularChainComplexFunctor C).obj R).map (TopCat.ofHom e.toFun)) := by
  let F := (singularChainComplexFunctor C).obj R
  let hX : TopCat.Homotopy
      (TopCat.ofHom e.toFun ≫ TopCat.ofHom e.invFun) (𝟙 X) := e.left_inv.some
  let hY : TopCat.Homotopy
      (TopCat.ofHom e.invFun ≫ TopCat.ofHom e.toFun) (𝟙 Y) := e.right_inv.some
  let E : _root_.HomotopyEquiv (F.obj X) (F.obj Y) :=
    { hom := F.map (TopCat.ofHom e.toFun)
      inv := F.map (TopCat.ofHom e.invFun)
      homotopyHomInvId := by
        rw [← F.map_comp, ← F.map_id X]
        exact hX.singularChainComplexFunctorObjMap R
      homotopyInvHomId := by
        rw [← F.map_comp, ← F.map_id Y]
        exact hY.singularChainComplexFunctorObjMap R }
  exact E.quasiIso_hom

private lemma isIso_unit_stdSimplex_zero :
    IsIso (sSetTopAdj.unit.app (Δ[0] : SSet.{w})) := by
  have (n : SimplexCategoryᵒᵖ) : IsIso ((sSetTopAdj.unit.app (Δ[0] : SSet.{w})).app n) := by
    apply (CategoryTheory.isIso_iff_bijective _).2
    constructor
    · intro a b _
      apply stdSimplex.objEquiv.injective
      apply SimplexCategory.Hom.ext
      apply OrderHom.ext
      funext i
      let : Subsingleton (Fin (⦋0⦌.len + 1)) := by
        change Subsingleton (Fin 1)
        infer_instance
      exact Subsingleton.elim _ _
    · intro a
      refine ⟨stdSimplex.objMk (OrderHom.const _ 0), ?_⟩
      apply ULift.ext
      apply TopCat.hom_ext
      ext z
      exact Subsingleton.elim _ _
  exact NatIso.isIso_of_isIso_app _

variable [CategoryWithHomology C]

/-- The actual map from a standard simplex to the terminal simplex is a quasi-isomorphism
on simplicial chains, by its extra degeneracy. -/
lemma quasiIso_chainComplexMap_stdSimplex_to_zero (n : ℕ) (R : C) :
    QuasiIso (chainComplexMap (stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{w})) R) := by
  let X := SSet.Augmented.stdSimplex.{w}.obj ⦋n⦌
  let ed := SSet.Augmented.StandardSimplex.extraDegeneracy.{w} ⦋n⦌
  let hT : IsTerminal ((SimplicialObject.const (Type w)).obj X.right) :=
    Functor.isTerminal (fun _ ↦ terminalIsTerminal)
  let e := hT.uniqueUpToIso stdSimplex.isTerminalObj₀
  have h : stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{w}) = X.hom ≫ e.hom :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  have : QuasiIso (chainComplexMap X.hom R) :=
    (extraDegeneracyChainHomotopyEquiv X ed R).quasiIso_hom
  rw [h]
  change QuasiIso (((chainComplexFunctor C).obj R).map (X.hom ≫ e.hom))
  rw [Functor.map_comp]
  infer_instance

/-- The actual simplicial-to-singular unit comparison on every standard simplex
is a quasi-isomorphism. -/
lemma quasiIso_realizationChainComparison_stdSimplex (n : ℕ) (R : C) :
    QuasiIso (realizationChainComparison (Δ[n] : SSet.{w}) R) := by
  let p := stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{w})
  let : ContractibleSpace (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
    Convexity.StdSimplex.contractibleSpace _
  let : ContractibleSpace (SSet.toTop.obj (Δ[n] : SSet.{w})) :=
    (SimplexCategory.toTopHomeo ⦋n⦌).contractibleSpace
  let e := ContinuousMap.homotopyEquivOfContractible (SSet.toTop.map p).hom
    ((SimplexCategory.toTopHomeo ⦋n⦌).symm (Convexity.StdSimplex.single 0))
  have : QuasiIso (((singularChainComplexFunctor C).obj R).map (SSet.toTop.map p)) :=
    quasiIso_singular_of_homotopyEquiv e R
  have : QuasiIso (chainComplexMap p R) := quasiIso_chainComplexMap_stdSimplex_to_zero n R
  have : IsIso (sSetTopAdj.unit.app (Δ[0] : SSet.{w})) := isIso_unit_stdSimplex_zero
  have : QuasiIso (realizationChainComparison (Δ[0] : SSet.{w}) R) := by
    change QuasiIso (((chainComplexFunctor C).obj R).map (sSetTopAdj.unit.app _))
    infer_instance
  have : QuasiIso (realizationChainComparison (Δ[n] : SSet.{w}) R ≫
      ((singularChainComplexFunctor C).obj R).map (SSet.toTop.map p)) := by
    rw [← realizationChainComparison_naturality]
    infer_instance
  exact quasiIso_of_comp_right _
    (((singularChainComplexFunctor C).obj R).map (SSet.toTop.map p))

end SSet
