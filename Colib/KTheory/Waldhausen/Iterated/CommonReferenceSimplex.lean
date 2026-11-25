/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/

module

public import Colib.KTheory.Waldhausen.Iterated.SimplexTriangleLift

/-!
# Complete common-reference simplex nodes

The simplex chain retains each original exact functor and its reference isomorphism.
The whole chain restricts, changes reference and postcomposes via those very data.
No equality of nodes is inferred merely from isomorphism of their functors.

Adapted from the original Quillen files under
`Quillen/Waldhausen/SConstruction/Iterated` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`:
`CommonReferenceFaces.lean:19-44`, `CommonReferenceNodeTransport.lean:18-27`,
and `CommonReferenceNerveWhiskering.lean:32-43`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
open scoped Simplicial
universe u

namespace CategoryTheory.Waldhausen.IteratedS.ModelSimplex

open SmallWaldhausenCategory

variable {V W T : WideSubcategory preservesZero.{u}}

/-- Restriction selects the original full dependent nodes in the face order. -/
theorem ofIsos_face {k l : ℕ} (F₀ : V ⟶ W) (F : Fin (k + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.hom.toFunctor ≅ (F i).hom.toFunctor) (α : ⦋l⦌ ⟶ ⦋k⦌) :
    (ofIsos F₀ F ρ).face α =
      ofIsos F₀ (fun i ↦ F (α.toOrderHom i)) (fun i ↦ ρ (α.toOrderHom i)) := by
  apply ext_diagram
  rfl

/-- Replacing the reference through its specified isomorphism preserves the whole chain. -/
theorem ofIsos_change_reference {k : ℕ} {F₀ F₁ : V ⟶ W}
    (e : F₀.hom.toFunctor ≅ F₁.hom.toFunctor) (F : Fin (k + 1) → (V ⟶ W))
    (ρ : ∀ i, F₁.hom.toFunctor ≅ (F i).hom.toFunctor) :
    ofIsos F₀ F (fun i ↦ e ≪≫ ρ i) = ofIsos F₁ F ρ := by
  apply ext_diagram
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro i j f
  apply heq_of_eq
  dsimp only [ofIsos]
  simp [Category.assoc]

/-- Congruence keeps the exact-functor and reference-isomorphism components together. -/
theorem ofIsos_nodes_congr {k : ℕ} {F₀ : V ⟶ W}
    (N M : Fin (k + 1) → Σ F : V ⟶ W, F₀.hom.toFunctor ≅ F.hom.toFunctor)
    (e : ∀ i, N i = M i) :
    ofIsos F₀ (fun i ↦ (N i).1) (fun i ↦ (N i).2) =
      ofIsos F₀ (fun i ↦ (M i).1) (fun i ↦ (M i).2) := by
  have h := funext e
  subst M
  rfl

/-- A functor equality and its actual reference equation identify the complete node. -/
theorem reference_node_eq {F₀ F G : V ⟶ W} (h : F.hom.toFunctor = G.hom.toFunctor)
    (ρ : F₀.hom.toFunctor ≅ F.hom.toFunctor) (σ : F₀.hom.toFunctor ≅ G.hom.toFunctor)
    (he : ρ.hom ≫ eqToHom h = σ.hom) :
    (⟨F, ρ⟩ : Σ H : V ⟶ W, F₀.hom.toFunctor ≅ H.hom.toFunctor) = ⟨G, σ⟩ := by
  have hFG : F = G := by
    apply WideSubcategory.hom_ext
    exact SmallWaldhausenCategory.Hom.ext h
  subst G
  have hρ : ρ = σ := Iso.ext (by simpa only [eqToHom_refl, Category.comp_id] using he)
  subst σ
  rfl

/-- Postcomposition retains every original vertex and its specified reference isomorphism. -/
theorem ofIsos_postcomp {k : ℕ} (F₀ : V ⟶ W) (F : Fin (k + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.hom.toFunctor ≅ (F i).hom.toFunctor) (J : W ⟶ T) :
    (ofIsos F₀ F ρ).postcomp J =
      ofIsos (F₀ ≫ J) (fun i ↦ F i ≫ J)
        (fun i ↦ isoWhiskerRight (ρ i) J.hom.toFunctor) := by
  apply ext_diagram
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro i j f
  apply heq_of_eq
  change whiskerRight ((ρ i).inv ≫ (ρ j).hom) J.hom.toFunctor =
    whiskerRight (ρ i).inv J.hom.toFunctor ≫ whiskerRight (ρ j).hom J.hom.toFunctor
  exact whiskerRight_comp _ _ _

end CategoryTheory.Waldhausen.IteratedS.ModelSimplex
