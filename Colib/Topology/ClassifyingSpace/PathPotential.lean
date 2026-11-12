/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.CompletionSurjectivity

/-!
# Natural path potentials control all realized paths

A natural transformation from a realized-arrow functor to a constant functor
extends to the actual groupoid completion. Surjectivity of the original
completed-arrow realization therefore gives its naturality formula along every
continuous path between original vertices, not merely along categorical edges.
-/

open Topology CategoryTheory

/-! Implementation source: `Quillen/Topology/ClassifyingSpace/PathPotential.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and original proofs are retained. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory
open scoped Topology
namespace Topology
variable {C : Type u} [Category.{v} C] {Y : Type w} [TopologicalSpace Y]

/-- A genuine potential on original edges controls every continuous vertex-to-vertex path. -/
theorem classifyingSpacePath_potential (f : C(ClassifyingSpace C, Y))
    (y : FundamentalGroupoid Y)
    (τ : classifyingFundamentalGroupoidFunctor C ⋙ FundamentalGroupoid.map f ⟶
      (Functor.const C).obj y)
    {c d : C} (p : Path (classifyingSpacePoint c) (classifyingSpacePoint d)) :
    (FundamentalGroupoid.map f).map (Path.Homotopic.Quotient.mk p) ≫ τ.app d = τ.app c := by
  let A := classifyingGroupoidCompletionFunctor C ⋙ FundamentalGroupoid.map f
  let B := (Functor.const (⊤ : MorphismProperty C).Localization).obj y
  let τ' : (⊤ : MorphismProperty C).Q ⋙ A ⟶ (⊤ : MorphismProperty C).Q ⋙ B :=
    (eqToHom (by dsimp only [A]; rw [← Functor.assoc, toClassifyingGroupoidCompletionFunctor])) ≫ τ
  let η : A ⟶ B := Localization.Construction.natTransExtension τ'
  obtain ⟨a, ha⟩ := classifyingGroupoidCompletionFunctor_map_surjective C c d
    (Path.Homotopic.Quotient.mk p)
  have h := η.naturality a
  have hc : η.app ((⊤ : MorphismProperty C).Q.obj c) = τ.app c := by
    simp [η, τ', Localization.Construction.NatTransExtension.app_eq]
  have hd : η.app ((⊤ : MorphismProperty C).Q.obj d) = τ.app d := by
    simp [η, τ', Localization.Construction.NatTransExtension.app_eq]
  rw [hc, hd] at h
  change (FundamentalGroupoid.map f).map ((classifyingGroupoidCompletionFunctor C).map a) ≫
    τ.app d = τ.app c ≫ 𝟙 y at h
  rw [ha] at h
  exact h.trans (Category.comp_id _)

end Topology
