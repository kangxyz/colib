/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceSimplex

/-!
# Actual reference transport of chosen-zero dependent nodes

Adapted from `Quillen/Waldhausen/SConstruction/Iterated/ModelReferenceReanchor.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
universe u
namespace CategoryTheory.Waldhausen.IteratedS.ModelSimplex
open SmallWaldhausenCategory

variable {V W : WideSubcategory preservesZero.{u}} {k : ℕ} {F₀ F₁ : V ⟶ W}

/-- Transport one original dependent reference node by the specified isomorphism. -/
def reanchorNode (e : F₀.hom.toFunctor ≅ F₁.hom.toFunctor)
    (N : Σ F : V ⟶ W, F₁.hom.toFunctor ≅ F.hom.toFunctor) :
    Σ F : V ⟶ W, F₀.hom.toFunctor ≅ F.hom.toFunctor :=
  ⟨N.1, e ≪≫ N.2⟩

/-- Reanchoring preserves each actual equality of full nodes. -/
theorem reanchorNode_congr (e : F₀.hom.toFunctor ≅ F₁.hom.toFunctor)
    {N M : Σ F : V ⟶ W, F₁.hom.toFunctor ≅ F.hom.toFunctor} (h : N = M) :
    reanchorNode e N = reanchorNode e M :=
  congrArg (reanchorNode e) h

/-- Two successive transports retain the original node and associate its references. -/
theorem reanchorNode_assoc {F₂ : V ⟶ W} (e : F₀.hom.toFunctor ≅ F₁.hom.toFunctor)
    (f : F₁.hom.toFunctor ≅ F₂.hom.toFunctor)
    (N : Σ G : V ⟶ W, F₂.hom.toFunctor ≅ G.hom.toFunctor) :
    reanchorNode e (reanchorNode f N) = reanchorNode (e ≪≫ f) N :=
  congrArg (fun η : F₀.hom.toFunctor ≅ N.1.hom.toFunctor ↦
    (⟨N.1, η⟩ : Σ G : V ⟶ W, F₀.hom.toFunctor ≅ G.hom.toFunctor))
    (Iso.trans_assoc e f N.2).symm

/-- The same model nodes with their reference comparisons transported from `F₁` to `F₀` by
composition with `e`.
-/
def reanchorNodes (e : F₀.hom.toFunctor ≅ F₁.hom.toFunctor)
    (N : Fin (k + 1) → Σ F : V ⟶ W, F₁.hom.toFunctor ≅ F.hom.toFunctor)
    (i : Fin (k + 1)) : Σ F : V ⟶ W, F₀.hom.toFunctor ≅ F.hom.toFunctor :=
  reanchorNode e (N i)

/-- The model simplex constructed from the given nodes using `F₀` as reference and the comparisons
transported along `e`.
-/
def reanchorSimplex (e : F₀.hom.toFunctor ≅ F₁.hom.toFunctor)
    (N : Fin (k + 1) → Σ F : V ⟶ W, F₁.hom.toFunctor ≅ F.hom.toFunctor) : ModelSimplex V W k :=
  ofIsos F₀ (fun i ↦ (reanchorNodes e N i).1) (fun i ↦ (reanchorNodes e N i).2)

theorem reanchorSimplex_eq (e : F₀.hom.toFunctor ≅ F₁.hom.toFunctor)
    (N : Fin (k + 1) → Σ F : V ⟶ W, F₁.hom.toFunctor ≅ F.hom.toFunctor) :
    reanchorSimplex e N = ofIsos F₁ (fun i ↦ (N i).1) (fun i ↦ (N i).2) :=
  ofIsos_change_reference e _ _

end CategoryTheory.Waldhausen.IteratedS.ModelSimplex
