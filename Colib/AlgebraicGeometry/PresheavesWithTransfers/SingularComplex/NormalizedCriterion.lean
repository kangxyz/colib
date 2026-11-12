/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Presheaf
public import Colib.AlgebraicTopology.DoldKan.NormalizedRepresentatives
import Mathlib.Algebra.Homology.Functor

/-!
# Checking a transfer singular comparison on normalized cycles

The pointwise normalized cycle and boundary criterion detects quasi-isomorphisms
of the original transfer complexes. Evaluation uses the same graph cofaces and
the same coefficient morphism in every degree.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

open AlgebraicTopology.NormalizedMooreComplex

variable {k : Type u} [Field k]
variable {P Q : PresheafWithTransfers.{v} k}

set_option quotPrecheck false in
local notation "S(" P₁ "," X ")" => (Cor.simplexProductCosimplicial X).op ⋙ (P₁).obj

set_option synthInstance.maxHeartbeats 80000 in
-- The exact inclusion and evaluation instances are synthesized in the two abelian categories.
/-- Reflection of normalized boundaries and surjectivity modulo normalized
boundaries at every smooth source imply the actual transfer quasi-isomorphism. -/
theorem singularComplexMap_quasiIso_of_normalized (η : P ⟶ Q)
    (hinj : ∀ (X : Cor k) (n : ℕ) (x : sections P (Cor.simplexProduct X n)),
      IsCycle (S(P,X)) n x →
      IsBoundary (S(Q,X)) n (η.hom.app (op (Cor.simplexProduct X n)) x) →
      IsBoundary (S(P,X)) n x)
    (hsurj : ∀ (X : Cor k) (n : ℕ) (y : sections Q (Cor.simplexProduct X n)),
      IsCycle (S(Q,X)) n y → ∃ x : sections P (Cor.simplexProduct X n),
        IsCycle (S(P,X)) n x ∧
          IsBoundary (S(Q,X)) n (y - η.hom.app (op (Cor.simplexProduct X n)) x)) :
    QuasiIso (singularComplexMap η) := by
  let : (AdditiveFunctor.forget (Cor k)ᵒᵖ AddCommGrpCat.{v}).ReflectsIsomorphisms :=
    (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{v}).fullyFaithfulι.reflectsIsomorphisms
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology (singularComplexMap η)
    (AdditiveFunctor.forget (Cor k)ᵒᵖ AddCommGrpCat.{v})).1
  apply (HomologicalComplex.quasiIso_iff_evaluation _).2
  intro U
  let φ : S(P,U.unop) ⟶ S(Q,U.unop) :=
    Functor.whiskerLeft (Cor.simplexProductCosimplicial U.unop).op η.hom
  change QuasiIso ((alternatingFaceMapComplex AddCommGrpCat).map φ)
  exact quasiIso_alternatingFaceMapComplex_of_normalized φ (hinj U.unop) (hsurj U.unop)

end AlgebraicGeometry.PresheafWithTransfers
