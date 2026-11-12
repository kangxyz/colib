module

import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.Projectivity

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

noncomputable section

example (A : Type u) [CommRing A] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of A)) (π : X ⟶ projectiveLine A) [IsFinite π]
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p) :
    ∃ (n : ℕ) (i : X ⟶ projectiveSpaceOver n (Spec (.of A))),
      IsClosedImmersion i ∧ i ≫ (projectiveSpaceOver n (Spec (.of A)) ↘ Spec (.of A)) = p :=
  isProjectiveMorphism_of_finite_projectiveLine A p π hπ

#print axioms AlgebraicGeometry.Scheme.isProjectiveMorphism_of_finite_projectiveLine
