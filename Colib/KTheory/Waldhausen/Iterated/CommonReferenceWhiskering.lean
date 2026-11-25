/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceSimplex

/-!
# Precomposition of the whole common-reference diagram

Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/CommonReferenceWhiskering.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor
universe u
namespace CategoryTheory.Waldhausen.IteratedS.ModelSimplex
open SmallWaldhausenCategory

variable {V W T : WideSubcategory preservesZero.{u}}

/-- Precomposition keeps all vertices and their actual reference transformations. -/
theorem ofIsos_precomp {k : ℕ} (F₀ : V ⟶ W) (F : Fin (k + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.hom.toFunctor ≅ (F i).hom.toFunctor) (J : T ⟶ V) :
    (ofIsos F₀ F ρ).precomp J =
      ofIsos (J ≫ F₀) (fun i ↦ J ≫ F i) (fun i ↦ isoWhiskerLeft J.hom.toFunctor (ρ i)) := by
  apply ext_diagram
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro i j f
  apply heq_of_eq
  change whiskerLeft J.hom.toFunctor ((ρ i).inv ≫ (ρ j).hom) =
    whiskerLeft J.hom.toFunctor (ρ i).inv ≫ whiskerLeft J.hom.toFunctor (ρ j).hom
  exact whiskerLeft_comp _ _ _

end CategoryTheory.Waldhausen.IteratedS.ModelSimplex
