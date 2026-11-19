/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.ParameterProduct
public import Colib.Algebra.Homology.SignedParameterConjugation

/-! # Native Nisnevich placement of the original parameter

The existing native declarations are housed here without topology-change dependencies.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicSimplex
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The original sheafified singular chains, before native cochain extension. -/
abbrev reducedTorusNisnevichOrdinaryChains (q : ℕ) :
    ChainComplex (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))
      AddCommGrpCat.{u + 1}) ℕ :=
  (sheafifiedSingularChainsFunctor k
    (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))).obj
      ((toPresheaf k).obj (reducedTorus k q))

/-- The original Nisnevich singular chains in nonpositive cochain degrees. -/
abbrev reducedTorusNisnevichOrdinaryCochain (q : ℕ) := (reducedTorusNisnevichOrdinaryChains k
    q).extend (ComplexShape.embeddingUpIntLE 0)

/-- The original Nisnevich parameter arrow with its native extension comparison. -/
def reducedTorusNisnevichParameterCochain (q : ℕ) :
    reducedTorusNisnevichOrdinaryCochain k q ⟶
      (((torusParameterSheafFunctor k)).mapHomologicalComplex (.up ℤ)).obj
          (reducedTorusNisnevichOrdinaryCochain k (q + 1)) :=
  (((ComplexShape.embeddingUpIntLE 0)).extendFunctor _).map
      (sheafifiedReducedTorusSingularParameterProduct k q) ≫
    (Stacks.DerivedIndexing.mapExtendIso (torusParameterSheafFunctor k)
        (ComplexShape.embeddingUpIntLE 0) (reducedTorusNisnevichOrdinaryChains k (q + 1))).hom

/-- The original Nisnevich ordinary cochains at their native negative weight. -/
abbrev reducedTorusNisnevichOrdinarySigned (q : ℕ) :=
  (reducedTorusNisnevichOrdinaryCochain k q)⟦-(q : ℤ)⟧

/-- Signed placement of the actual Nisnevich parameter arrow. -/
def reducedTorusNisnevichParameterSigned (q : ℕ) :
    reducedTorusNisnevichOrdinarySigned k q ⟶
      (((torusParameterSheafFunctor k).mapHomologicalComplex (.up ℤ))).obj
          ((reducedTorusNisnevichOrdinarySigned k (q + 1))⟦(1 : ℤ)⟧) :=
  signedParameterArrow ((torusParameterSheafFunctor k).mapHomologicalComplex (.up ℤ))
      (reducedTorusNisnevichParameterCochain k q)
    (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) (by omega) (Iso.refl _) (Iso.refl _)

end AlgebraicGeometry.PresheafWithTransfers
