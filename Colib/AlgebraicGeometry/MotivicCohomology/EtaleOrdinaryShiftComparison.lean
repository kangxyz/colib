/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.OrdinaryShiftComparison
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.EtaleChangeOfTopology
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.DerivedChangeOfTopology

/-! # The actual étale motivic complex as signed ordinary singular chains

The canonical Nisnevich-to-étale change of topology commutes with the original
singular chains and their signed shift. No alternate motivic complex is defined.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicSimplex
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- Successive Nisnevich and étale sheafification on the actual ordinary chains. -/
def singularChainsChangeOfTopologyIso
    (P : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    ((SmoothSite.nisnevichToEtaleSheaf (Spec (CommRingCat.of k))
      AddCommGrpCat.{u + 1}).mapHomologicalComplex (.down ℕ)).obj
        ((sheafifiedSingularChainsFunctor k
          (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))).obj P) ≅
      (sheafifiedSingularChainsFunctor k
        (SmoothSite.etaleTopology (Spec (CommRingCat.of k)))).obj P :=
  (Functor.mapHomologicalComplexCompIso
    (SmoothSite.nisnevichToEtaleSheafificationIso (Spec (CommRingCat.of k)))
      (.down ℕ)).app ((singularChainsFunctor k).obj P)

/-- The actual étale motivic complex retains the native signed shift by `-q`. -/
def motivicEtaleSheafComplexOrdinaryShiftIso (q : ℕ) :
    motivicEtaleSheafComplex k q ≅
      (((sheafifiedSingularChainsFunctor k
        (SmoothSite.etaleTopology (Spec (CommRingCat.of k)))).obj
          ((toPresheaf k).obj (reducedTorus k q))).extend
            (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧ := by
  let F := SmoothSite.nisnevichToEtaleSheaf (Spec (CommRingCat.of k))
    AddCommGrpCat.{u + 1}
  let K := (sheafifiedSingularChainsFunctor k
    (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))).obj
      ((toPresheaf k).obj (reducedTorus k q))
  let e := ComplexShape.embeddingUpIntLE 0
  exact (F.mapHomologicalComplex (.up ℤ)).mapIso
      (motivicSheafComplexOrdinaryShiftIso k q) ≪≫
    ((F.mapHomologicalComplex (.up ℤ)).commShiftIso (-(q : ℤ))).app (K.extend e) ≪≫
    (shiftFunctor _ (-(q : ℤ))).mapIso
      ((Stacks.DerivedIndexing.mapExtendIso F e K).symm ≪≫
        (e.extendFunctor _).mapIso
          (singularChainsChangeOfTopologyIso k ((toPresheaf k).obj (reducedTorus k q))))

end AlgebraicGeometry.PresheafWithTransfers
