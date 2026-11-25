/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.ModelReferenceReanchor
public import Colib.Topology.ClassifyingSpace.Contraction
public import Mathlib.CategoryTheory.CodiscreteCategory

/-!
# The nerve of full reference nodes

The parameter nerve retains the exact reference isomorphism at each Waldhausen model map.
Its canonical node contracts this same realization. The attachment is postcomposition
followed by reanchoring along the specified isomorphism.

Adapted from `CommonReferenceNerve`, `CommonReferenceNerveCubeExtension`, and
`CommonReferenceNerveCompactAttachment` in Quillen K-theory at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
This module constructs the parameter space and its actual characteristic simplices.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
open SmallWaldhausenCategory

variable {V W T : WideSubcategory preservesZero.{u}}

/-- A model map together with its complete specified reference isomorphism. -/
abbrev Node (F : V ⟶ W) := Σ K : V ⟶ W, F.hom.toFunctor ≅ K.hom.toFunctor

/-- The actual simplicial nerve of the full dependent reference nodes. -/
abbrev parameterSSet (F : V ⟶ W) : SSet.{u} :=
  nerve (Codiscrete (Node F))

/-- The canonical node retains the identity comparison of the original map. -/
def referenceNode (F : V ⟶ W) : Codiscrete (Node F) :=
  ⟨⟨F, Iso.refl _⟩⟩

/-- The displayed canonical node is initial in this actual codiscrete category. -/
def referenceNodeInitial (F : V ⟶ W) : IsInitial (referenceNode F) :=
  IsInitial.ofUnique _

/-- The actual parameter realization is contractible at the canonical reference node. -/
theorem parameter_contractible (F : V ⟶ W) : ContractibleSpace |parameterSSet F| :=
  classifyingSpace_contractible_of_isInitial (referenceNodeInitial F)

/-- Postcompose the node and retain the specified reanchoring isomorphism. -/
def attachPostcompNode (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
    (ε : G.hom.toFunctor ≅ (F ≫ J).hom.toFunctor) (N : Node F) : Node G :=
  ⟨N.1 ≫ J, ε ≪≫ isoWhiskerRight N.2 J.hom.toFunctor⟩

/-- Realize the nerve map induced by a function on full reference nodes. -/
def mapParameter {U : WideSubcategory preservesZero.{u}} {F : V ⟶ W} {G : U ⟶ T}
    (f : Node F → Node G) :
    C(|parameterSSet F|, |parameterSSet G|) :=
  (SSet.toTop.map (nerveMap (Codiscrete.functorOfFun f))).hom

/-- The actual nerve map of the specified postcomposition and reanchoring. -/
def attaching (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
    (ε : G.hom.toFunctor ≅ (F ≫ J).hom.toFunctor) :
    parameterSSet F ⟶ parameterSSet G :=
  nerveMap (Codiscrete.functorOfFun (attachPostcompNode F J G ε))

/-- Realization is exactly the continuous map on the full reference parameters. -/
theorem attaching_realization (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
    (ε : G.hom.toFunctor ≅ (F ≫ J).hom.toFunctor) :
    (SSet.toTop.map (attaching F J G ε)).hom =
      mapParameter (attachPostcompNode F J G ε) := rfl

variable (F₀ : V ⟶ W)

/-- The reference isomorphisms determine the actual transformation on every nerve arrow. -/
def diagram : Codiscrete (Node F₀) ⥤ (V.obj.Obj ⥤ W.obj.Obj) where
  obj i := i.as.1.hom.toFunctor
  map {i j} _ := i.as.2.inv ≫ j.as.2.hom
  map_id i := by simp
  map_comp f g := by simp [Category.assoc]

/-- Every original nerve chain is its exact common-reference model simplex. -/
def chain {k : ℕ} (c : Fin (k + 1) ⥤ Codiscrete (Node F₀)) : ModelSimplex V W k :=
  ModelSimplex.ofIsos F₀ (fun i ↦ (c.obj i).as.1) (fun i ↦ (c.obj i).as.2)

/-- The simplex diagram is literally the original chain followed by the reference diagram. -/
theorem chain_diagram {k : ℕ} (c : Fin (k + 1) ⥤ Codiscrete (Node F₀)) :
    (chain F₀ c).diagram = c ⋙ diagram F₀ := rfl

/-- Reindexing the nerve chain preserves the whole original simplex face. -/
theorem chain_face {k l : ℕ} (c : Fin (k + 1) ⥤ Codiscrete (Node F₀))
    (α : ⦋l⦌ ⟶ ⦋k⦌) :
    chain F₀ (α.toOrderHom.monotone.functor ⋙ c) = (chain F₀ c).face α := by
  apply ModelSimplex.ext_diagram
  rfl

/-- The actual nerve simplex of a full original node list; its labels need no global order. -/
def simplexMap {k : ℕ} (N : Fin (k + 1) → Node F₀) :
    Δ[k] ⟶ nerve (Codiscrete (Node F₀)) :=
  SSet.yonedaEquiv.symm (Codiscrete.functor N)

/-- Every nerve coordinate retains the entire original dependent node. -/
theorem simplexMap_obj {k : ℕ} (N : Fin (k + 1) → Node F₀)
    (n : SimplexCategoryᵒᵖ) (τ : (Δ[k]).obj n) (i : Fin (n.unop.len + 1)) :
    (((simplexMap F₀ N).app n τ).obj i).as = N (τ.down.toOrderHom i) := rfl

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
