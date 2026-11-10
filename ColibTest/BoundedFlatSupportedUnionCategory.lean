/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedOpenSupport

/-! Actual support, unchanged quotient and category consumers without compactness assumptions. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.Fibration AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u
attribute [local instance] Abelian.hasFiniteBiproducts

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

example (K : CochainComplex X.Modules ℤ) :
    boundedAboveFlatPerfectSupported (T ⊔ j.opensRange).ι K ↔
      boundedAboveFlatPerfectSupported T.ι K ∧
        (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj K).Acyclic :=
  boundedAboveFlatPerfectSupported_sup_opensRange_iff j T K

example (K : AcyclicCategory (boundedAboveFlatPerfectSupportedOpenNested j T)) :
    ((boundedAboveFlatPerfectSupportedOpenAcyclicSupportedEquivalence j T).functor.obj K).obj =
      K.obj.obj := rfl

example {K L : AcyclicCategory (boundedAboveFlatPerfectSupportedOpenNested j T)} (f : K ⟶ L) :
    ((boundedAboveFlatPerfectSupportedOpenAcyclicSupportedEquivalence j T).functor.map f).hom =
      f.hom.hom := rfl

example (K : (boundedAboveFlatPerfectSupported (T ⊔ j.opensRange).ι).FullSubcategory) :
    ((boundedAboveFlatPerfectSupportedOpenAcyclicSupportedEquivalence j T).inverse.obj K).obj.obj =
      K.obj := rfl

example {A B : AcyclicCategory (boundedAboveFlatPerfectSupportedOpenNested j T)} (f : A ⟶ B)
    (hf : (acyclicStructure (boundedAboveFlatPerfectSupportedOpenNested j T)).cof f) :
    (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι).cof
      ((boundedAboveFlatPerfectSupportedOpenAcyclicToSupported j T).map f) :=
  boundedAboveFlatPerfectSupportedOpenAcyclicToSupported_cofibration j T f hf

example {A B : AcyclicCategory (boundedAboveFlatPerfectSupportedOpenNested j T)} (f : A ⟶ B)
    (Q : CochainComplex X.Modules ℤ) (hQ : boundedAboveFlatPerfectSupported T.ι Q)
    (q : B.obj.obj ⟶ Q) (w : f.hom.hom ≫ q = 0)
    (hS : (ShortComplex.mk f.hom.hom q w).ShortExact) :
    boundedAboveFlatPerfectSupported (T ⊔ j.opensRange).ι Q := by
  apply (boundedAboveFlatPerfectSupported_sup_opensRange_iff j T Q).2
  refine ⟨hQ, ?_⟩
  exact (perfectSupported_X₃_of_shortExact j hS
    ⟨A.obj.property.1.1,
      (boundedAboveFlatPerfectSupportedOpenAcyclic_iff j T A.obj).1 A.property⟩
    ⟨B.obj.property.1.1,
      (boundedAboveFlatPerfectSupportedOpenAcyclic_iff j T B.obj).1 B.property⟩).2

example :
    IsZero ((boundedAboveFlatPerfectSupportedUnionToAcyclic j T).obj
      (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι).zero) :=
  (boundedAboveFlatPerfectSupportedUnionToAcyclic_exact j T).zero
    (boundedAboveFlatPerfectSupportedWaldhausen (T ⊔ j.opensRange).ι).isZero

example :
    boundedAboveFlatPerfectSupportedUnionToAcyclic j T ⋙
        acyclicInclusion (boundedAboveFlatPerfectSupportedOpenNested j T) =
      ObjectProperty.ιOfLE
        (show boundedAboveFlatPerfectSupported (T ⊔ j.opensRange).ι ≤
          boundedAboveFlatPerfectSupported T.ι from fun K h =>
            ((boundedAboveFlatPerfectSupported_sup_opensRange_iff j T K).1 h).1) :=
  boundedAboveFlatPerfectSupportedUnionToAcyclic_comp_inclusion j T
