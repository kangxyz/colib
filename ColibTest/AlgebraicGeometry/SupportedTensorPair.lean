/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedCoefficientSmallModel
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.RingedSpace Topology.LoopPrespectrum
open scoped Simplicial
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorPairTest

namespace T0
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
example (r : (Γ(X, ⊤))ˣ) :
    Functor.whiskerRight (boundedAboveFlatPerfectSupportedTensorUnitAutomorphism j r).hom
        (tensorCoefficientSupportedForget j) ≫ (tensorSupportedForgetIso j).hom =
      (tensorSupportedForgetIso j).hom ≫
        Functor.whiskerLeft (tensorCoefficientSupportedForget j)
          (boundedAboveFlatPerfectTensorUnitAutomorphism X r).hom :=
  tensorSupportedForget_unit j r
end T0

namespace T1
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)
example :
    IsExact (boundedAboveFlatPerfectSupportedWaldhausen B.hom).cof
      (boundedAboveFlatPerfectSupportedWaldhausen B.hom).weq
      (boundedAboveFlatPerfectSupportedWaldhausen A.hom).cof
      (boundedAboveFlatPerfectSupportedWaldhausen A.hom).weq (tensorSupportedPairFunctor p) :=
  tensorSupportedPair_exact p
end T1

namespace T2
variable {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B)
example (r : (Γ(A.right, ⊤))ˣ) :
    Functor.whiskerRight (tensorSupportedPairAutomorphism p r).hom
        (tensorCoefficientSupportedForget A.hom) ≫ (tensorSupportedPairForgetIso p).hom =
      (tensorSupportedPairForgetIso p).hom ≫
        Functor.whiskerLeft (tensorCoefficientSupportedForget B.hom)
          (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism p.right r).hom :=
  tensorSupportedPairForget_unit p r
end T2

namespace T3
variable {S T : Scheme.OpenPairs.{u}} (p : S ⟶ T)
example (r : (Γ(S.right, ⊤))ˣ) :
    (tensorSupportedPairFirstRowNormalizedAutomorphism p r).hom =
      whiskerRight (normalizedWeakTransformation (tensorSupportedPair_exact p)
        (tensorSupportedPair_exact p)
        (tensorSupportedPairAutomorphism p r).hom)
        (oneEmbedding (boundedAboveFlatPerfectSupportedWaldhausen S.hom)) :=
  tensorSupportedPairFirstRowNormalizedAutomorphism_hom p r
end T3

namespace T4
variable {S T : Scheme.OpenPairs.{u}} (p : S ⟶ T)
example
    (r : (Γ(S.right, ⊤))ˣ)
    (A : (asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen T.hom)).obj.Obj) :
    (asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen S.hom)).obj.waldhausen.weq
      ((tensorSupportedPairModelTransformation p r).app A) :=
  tensorSupportedPairModelTransformation_weak p r A
end T4

end AlgebraicGeometry.Scheme.Modules.SupportedTensorPairTest
