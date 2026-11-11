module

import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedPairDiagram

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
universe u

variable {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} (j : U ⟶ X.unop) [IsOpenImmersion j]

example : (boundedAboveFlatGlobalSupportedEvaluation j).IsEquivalence := inferInstance

example : boundedAboveFlatGlobalSectionSupported j
    (boundedAboveFlatGlobalSectionWaldhausen X).zero := boundedAboveFlatGlobalZero_supported j

example : IsZero ((boundedAboveFlatGlobalSupportedEvaluation j).obj
    (boundedAboveFlatGlobalSupportedZero j)) :=
  boundedAboveFlatGlobalSupportedZero_evaluation_isZero j

example {A B : Scheme.OpenPairs.{u}} (g : A ⟶ B) :
    boundedAboveFlatGlobalSupportedPairReindex g ⋙
        (boundedAboveFlatGlobalSectionSupported (X := op A.right) A.hom).ι =
      (boundedAboveFlatGlobalSectionSupported (X := op B.right) B.hom).ι ⋙
        boundedAboveFlatGlobalSectionsMap g.right.op :=
  boundedAboveFlatGlobalSupportedPairReindex_forget g

example : pairSupported.{u} ⟶ pairAmbient := pairForget

example {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] :
    ParameterModels.supported f ⟶ ParameterModels.ambient Q := ParameterModels.forget f
