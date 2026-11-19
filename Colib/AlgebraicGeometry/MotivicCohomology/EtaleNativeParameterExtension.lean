/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.NativeNisnevichParameter
public import Colib.AlgebraicGeometry.MotivicCohomology.EtaleParameterChainSquare
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.ParameterChangeOfTopologyShift
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleSignedPlacement
public import Colib.Algebra.Homology.ParameterExtensionTransport

/-! # Native topology change on the extended original parameter maps

The extension uses the actual topology-change square and retains the native
double-sheafification endpoint isomorphisms and the one-way comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor AlgebraicSimplex
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]
/-- Native extension followed by the actual topology-change chain isomorphism. -/
def reducedTorusEtaleTopologyCochainIso (q : ℕ) :
    (((SmoothSite.nisnevichToEtaleSheaf (Spec (CommRingCat.of k)) AddCommGrpCat.{u +
        1})).mapHomologicalComplex (.up ℤ)).obj (reducedTorusNisnevichOrdinaryCochain k q) ≅
      reducedTorusEtaleOrdinaryCochain k q :=
  (Stacks.DerivedIndexing.mapExtendIso (SmoothSite.nisnevichToEtaleSheaf (Spec (CommRingCat.of k))
      AddCommGrpCat.{u + 1}) (ComplexShape.embeddingUpIntLE 0) (reducedTorusNisnevichOrdinaryChains
      k q)).symm ≪≫
    (((ComplexShape.embeddingUpIntLE 0)).extendFunctor _).mapIso
        (((Functor.mapHomologicalComplexCompIso (SmoothSite.nisnevichToEtaleSheafificationIso (Spec
        (CommRingCat.of k))) (.down ℕ))).app ((singularChainsFunctor k).obj ((toPresheaf k).obj
        (reducedTorus k q))))

/-- Change of topology of the original parameter cochain retains its native square. -/
theorem reducedTorusEtaleTopologyCochainSquare (q : ℕ) :
    (((SmoothSite.nisnevichToEtaleSheaf (Spec (CommRingCat.of k)) AddCommGrpCat.{u +
        1})).mapHomologicalComplex (.up ℤ)).map (reducedTorusNisnevichParameterCochain k q) ≫
      (NatTrans.mapHomologicalComplex (SmoothSite.parameterNisnevichToEtaleComparison (Spec
          (CommRingCat.of k)) AddCommGrpCat.{u + 1} (SmoothSite.multiplicativeGroupObject (Spec
          (CommRingCat.of k)))) (.up ℤ)).app
        (reducedTorusNisnevichOrdinaryCochain k (q + 1)) ≫
      (((reducedTorusEtaleParameterFunctor k)).mapHomologicalComplex (.up ℤ)).map
          (reducedTorusEtaleTopologyCochainIso k (q + 1)).hom =
    (reducedTorusEtaleTopologyCochainIso k q).hom ≫ reducedTorusEtaleParameterCochain k q := by
  exact
    (Stacks.DerivedIndexing.parameterSquare_extend (SmoothSite.nisnevichToEtaleSheaf (Spec
        (CommRingCat.of k)) AddCommGrpCat.{u + 1}) (torusParameterSheafFunctor k)
        (reducedTorusEtaleParameterFunctor k) (SmoothSite.parameterNisnevichToEtaleComparison (Spec
        (CommRingCat.of k)) AddCommGrpCat.{u + 1} (SmoothSite.multiplicativeGroupObject (Spec
        (CommRingCat.of k)))) (ComplexShape.embeddingUpIntLE 0)
      (sheafifiedReducedTorusSingularParameterProduct k q)
      (etaleReducedTorusSingularParameterProduct k q) (((Functor.mapHomologicalComplexCompIso
          (SmoothSite.nisnevichToEtaleSheafificationIso (Spec (CommRingCat.of k))) (.down ℕ))).app
          ((singularChainsFunctor k).obj ((toPresheaf k).obj (reducedTorus k q)))).hom
          (((Functor.mapHomologicalComplexCompIso (SmoothSite.nisnevichToEtaleSheafificationIso
          (Spec (CommRingCat.of k))) (.down ℕ))).app ((singularChainsFunctor k).obj ((toPresheaf
          k).obj (reducedTorus k (q + 1))))).hom
      (sheafifiedReducedTorusSingularParameterProduct_etale_square k q))

end AlgebraicGeometry.PresheafWithTransfers
