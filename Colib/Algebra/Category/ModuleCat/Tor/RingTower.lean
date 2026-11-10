/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Category.ModuleCat.Tor.ChangeOfRings

/-!
# Tor change of rings for literal ring towers and coefficient maps

This direct consumer keeps the given maps `R → B → A` and `R → C` in the
actual native Tor arguments. In particular the first source argument is the
`A`-module restricted along the literal composite `g.comp f`, and the coefficient
is `C` restricted along the literal map `φ`. Native restriction composition,
which acts as the identity on elements, is the only extra comparison.

The output coefficient is still the actual native extension `B ⊗_R C`.
No quotient `D`, quotient comparison, leading regular block, geometric Tor
vanishing, finite length, or remaining Koszul sequence is assumed or constructed.

This is the ring-tower step required by the original migration target in
Motivic commit `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/IncidenceTorReduction.lean:33-124`.
It is not a proof of that geometric endpoint. The restriction comparison is
Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`,
`Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:248-254`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleCat.Tor

variable {R B A C : Type u} [CommRing R] [CommRing B] [CommRing A] [CommRing C]

/-- Change rings in every degree for the actual maps `R → B → A` and `R → C`.
The only acyclicity hypothesis concerns the pair `(B,C)` over `R`. -/
def ringTowerIsoOfIsZeroTor (f : R →+* B) (g : B →+* A) (φ : R →+* C)
    (h : ∀ i : ℕ, 0 < i → IsZero
      (((CategoryTheory.Tor (ModuleCat.{u} R) i).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))).obj
          ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C)))) (n : ℕ) :
    ((CategoryTheory.Tor (ModuleCat.{u} R) n).obj
      ((ModuleCat.restrictScalars (g.comp f)).obj (ModuleCat.of A A))).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C)) ≅
      (ModuleCat.restrictScalars f).obj
        (((CategoryTheory.Tor (ModuleCat.{u} B) n).obj
          ((ModuleCat.restrictScalars g).obj (ModuleCat.of A A))).obj
            ((ModuleCat.extendScalars.{u, u, u} f).obj
              ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C)))) :=
  ((CategoryTheory.Tor (ModuleCat.{u} R) n).mapIso
    (ModuleCat.restrictScalarsComp'App f g (g.comp f) rfl (ModuleCat.of A A))).app
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C)) ≪≫
    changeOfRingsIsoOfIsZeroTor f
      ((ModuleCat.restrictScalars g).obj (ModuleCat.of A A))
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C)) h n

end ModuleCat.Tor
