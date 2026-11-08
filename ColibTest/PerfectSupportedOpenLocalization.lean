/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenLongExactSequence

/-! # Full-signature consumers for arbitrary supported relative-open localization -/

noncomputable section
open CategoryTheory CategoryTheory.Limits Waldhausen Fibration AlgebraicGeometry Topology
open AlgebraicGeometry.Scheme.Modules
universe u
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

example (n : ℕ) :
    (perfectSupportedOpenKMap j T (n + 1)).range =
      (perfectSupportedOpenConnectingHom j T n).ker ∧
    (perfectSupportedOpenConnectingHom j T n).range = (perfectSupportedUnionKMap j T n).ker ∧
    (perfectSupportedUnionKMap j T n).range = (perfectSupportedOpenKMap j T n).ker :=
  perfectSupportedOpen_positiveLongExactSequence j T n

example :
    (perfectSupportedOpenKMap j T 1).range = (perfectSupportedOpenConnectingHom j T 0).ker ∧
    (perfectSupportedOpenConnectingHom j T 0).range = (perfectSupportedUnionKMap j T 0).ker ∧
    (perfectSupportedUnionKMap j T 0).range = (perfectSupportedOpenKMap j T 0).ker :=
  perfectSupportedOpen_zeroLongExactSequence j T

example :
    (perfectSupportedOpenConnectingHom j T 0).range = (perfectSupportedUnionKMap j T 0).ker ∧
    (perfectSupportedUnionKMap j T 0).range = (perfectSupportedOpenKMap j T 0).ker ∧
    Function.Surjective (perfectSupportedOpenKMap j T 0) :=
  perfectSupportedOpen_relativeKZeroTail j T

example (n : ℕ) :
    (perfectSupportedOpenKRestrict j T n).comp (perfectSupportedOpenKMap j T n) =
      perfectSupportedKRestrict j T n :=
  perfectSupportedOpenKRestrict_comp_perfectSupportedOpenKMap j T n

example (n : ℕ) :
    (perfectSupportedOpenAcyclicSupportedKEquiv j T n).toMonoidHom =
      KMap (perfectSupportedOpenAcyclicToSupported_exact j T) n :=
  perfectSupportedOpenAcyclicSupportedKEquiv_toMonoidHom j T n

example (n : ℕ) :
    (perfectSupportedUnionKMap j T n).comp
      (perfectSupportedOpenAcyclicSupportedKEquiv j T n).toMonoidHom =
      KMap (acyclicInclusion_exact (perfectSupportedOpenNested j T)) n :=
  perfectSupportedOpenAcyclicSupportedKEquiv_inclusion j T n

example (n : ℕ) : Function.Bijective (perfectSupportedUnionFiberKMap j T n) :=
  perfectSupportedUnionFiberKMap_bijective j T n

example (n : ℕ) (a : PerfectSupportedOpenCoarseK j T (n + 1)) :
    perfectSupportedUnionFiberKMap j T n (perfectSupportedOpenConnectingHom j T n a) =
      HomotopyFiber.connectingHom (changeWeakMap (perfectSupportedOpenNested j T))
        (perfectSupportedOpenWeakWaldhausen j T).kBasepoint
        (perfectSupportedWaldhausen T.ι).kBasepoint
        (changeWeakMap_basepoint (perfectSupportedOpenNested j T)) n a :=
  perfectSupportedUnionFiberKMap_connecting j T n a

example (n : ℕ) :
    (HomotopyGroup.piMap n
      (HomotopyFiber.projection (changeWeakMap (perfectSupportedOpenNested j T))
      (perfectSupportedOpenWeakWaldhausen j T).kBasepoint)
      (HomotopyFiber.projection_basepoint _ _ (perfectSupportedWaldhausen T.ι).kBasepoint
        (changeWeakMap_basepoint (perfectSupportedOpenNested j T)))).comp
      (perfectSupportedUnionFiberKMap j T n) = perfectSupportedUnionKMap j T n :=
  perfectSupportedUnionFiberKMap_projection j T n

example (K : CochainComplex X.Modules ℤ) :
    perfectSupported (T ⊔ j.opensRange).ι K ↔ perfectSupported T.ι K ∧
      (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic :=
  perfectSupported_sup_opensRange_iff j T K

example {K L : (perfectSupported T.ι).FullSubcategory} (f : K ⟶ L) :
    (perfectSupportedOpenWeakWaldhausen j T).weq f ↔
      QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom) :=
  perfectSupportedOpenWeakWaldhausen_weq_iff j T f

example {K L : AcyclicCategory (perfectSupportedOpenNested j T)} (f : K ⟶ L) :
    ((perfectSupportedOpenAcyclicToSupported j T).map f).hom = f.hom.hom :=
  perfectSupportedOpenAcyclicToSupported_map j T f

example :
    Waldhausen.IsExact (perfectSupportedWaldhausen T.ι).cof
      (perfectSupportedWaldhausen T.ι).weq (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).cof
      (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).weq (perfectSupportedRestrict j T) :=
  perfectSupportedRestrict_exact j T

example :
    IsWeakHomotopyEquivalence (canonicalFiberMap (perfectSupportedOpenNested j T)) :=
  perfectSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence j T

example : RowFactorization.SecondEndpointSection (perfectSupportedOpenNested j T)
    (perfectSupportedOpenJointData j T) :=
  perfectSupportedOpenJointData_secondEndpointSection j T

example : ExtensionAxiom (perfectSupportedOpenWeakWaldhausen j T) :=
  perfectSupportedOpenWeakWaldhausen_extensionAxiom j T

example :
    perfectSupportedOpenAcyclicToSupported j T ⋙ perfectSupportedUnionToAcyclic j T =
      𝟭 (AcyclicCategory (perfectSupportedOpenNested j T)) :=
  perfectSupportedOpenAcyclicToSupported_comp_inverse j T

example :
    perfectSupportedUnionToAcyclic j T ⋙ perfectSupportedOpenAcyclicToSupported j T =
      𝟭 ((perfectSupported (T ⊔ j.opensRange).ι).FullSubcategory) :=
  perfectSupportedUnionToAcyclic_comp_inverse j T

example :
    perfectSupportedUnionToAcyclic j T ⋙ acyclicInclusion (perfectSupportedOpenNested j T) =
      ObjectProperty.ιOfLE
        (show perfectSupported (T ⊔ j.opensRange).ι ≤ perfectSupported T.ι from fun K h =>
          ((perfectSupported_sup_opensRange_iff j T K).mp h).1) :=
  perfectSupportedUnionToAcyclic_comp_inclusion j T

example (n : ℕ) :
    (perfectSupportedKMap (j ⁻¹ᵁ T).ι n).comp (perfectSupportedKRestrict j T n) =
      (KMap (perfectComplexesRestrictOpenImmersion_isExact j) n).comp
        (perfectSupportedKMap T.ι n) :=
  perfectSupportedKRestrict_comp_forget j T n

example (V : X.Opens) (K : CochainComplex X.Modules ℤ) :
    (((restrictFunctor (V ⊔ T).ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic ↔
      (((restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic ∧
      (((restrictFunctor T.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic :=
  restrictAcyclic_sup_iff V T K

example (K : CochainComplex X.Modules ℤ)
    (h : (((restrictFunctor T.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic) :
    (((restrictFunctor (j ⁻¹ᵁ T).ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).Acyclic :=
  restrictAcyclic_preimage j T K h
