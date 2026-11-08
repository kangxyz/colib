module

/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberFineProjectionCubePath
public import Colib.KTheory.Waldhausen.Additivity.SeparatedFirstPiSurjectivity

/-!
# Class-level descent through the actual scalar projection input

Every original K-class has a representative obtained by the actual forward separated first map
on an original subdivision cube. Consequently a property, or equality of homomorphisms, proved
on all such input classes descends to every original class. The representative hypothesis is
explicit; it does not follow from this lemma and must retain any required geometric Theta and
canonical-null comparison in its own proof.
-/
/-! Adapted from
`Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarCofiberInputDescent.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; actual forward maps and signs are retained. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology SSet
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
open scoped Simplicial Topology
universe u v
namespace AlgebraicGeometry.Scheme.Modules
variable (X : Scheme.{u}) (n : ℕ)

/-- The literal scalar projection input classes cover the entire original K-group. -/
theorem perfectScalarProjectionInputCube_class_surjective
    (a : (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K n) :
    ∃ p : GenLoop (Fin (n + 1))
      |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet
        (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|
      (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)),
      (⟦perfectScalarProjectionInputCube n p⟧ :
        (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K n) = a :=
  separatedFirstCube_class_surjective (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace) n a

/-- A supplied class property descends only after it is proved on every actual input cube. -/
theorem perfectScalarProjectionInputCube_forall
    (P : (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K n → Prop)
    (h : ∀ p : GenLoop (Fin (n + 1))
      |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet
        (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|
      (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)),
      P ⟦perfectScalarProjectionInputCube n p⟧) :
    ∀ a, P a := by
  intro a
  obtain ⟨p, hp⟩ := perfectScalarProjectionInputCube_class_surjective X n a
  rw [← hp]
  exact h p

/-- An explicit equality on all literal input classes determines the original homomorphisms. -/
theorem perfectScalarProjectionInputCube_hom_ext {G : Type v} [Monoid G]
    (f g : (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K n →* G)
    (h : ∀ p : GenLoop (Fin (n + 1))
      |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet
        (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|
      (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)),
      f ⟦perfectScalarProjectionInputCube n p⟧ = g ⟦perfectScalarProjectionInputCube n p⟧) :
    f = g := by
  apply MonoidHom.ext
  exact perfectScalarProjectionInputCube_forall X n (fun a ↦ f a = g a) h

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarCofiberInputDescent.lean:1-59"
  "adaptation" "Actual forward input coverage and positive relative supported boundary"]
  AlgebraicGeometry.Scheme.Modules.perfectScalarProjectionInputCube_class_surjective
  AlgebraicGeometry.Scheme.Modules.perfectScalarProjectionInputCube_forall
  AlgebraicGeometry.Scheme.Modules.perfectScalarProjectionInputCube_hom_ext

attribute [colib_tag "COL-0329"]
  AlgebraicGeometry.Scheme.Modules.perfectScalarProjectionInputCube_class_surjective
  AlgebraicGeometry.Scheme.Modules.perfectScalarProjectionInputCube_forall
  AlgebraicGeometry.Scheme.Modules.perfectScalarProjectionInputCube_hom_ext
