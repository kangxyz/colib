/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedCoefficientAutomorphism
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open AlgebraicGeometry.RingedSpace
open scoped Simplicial ZeroObject
universe u
namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorRowTest
noncomputable section
variable {U X : Scheme.{u}} (ι : U ⟶ X) [IsOpenImmersion ι]

example
    (K : (boundedAboveFlatPerfectSupported ι).FullSubcategory)
    (i : Fin 2) :
    IsZero (((boundedAboveFlatPerfectSupportedTensorUnitRows ι).obj K).obj (interval i i le_rfl)) :=
  boundedAboveFlatPerfectSupportedTensorUnitRows_zero ι K i

example
    (K : (boundedAboveFlatPerfectSupported ι).FullSubcategory) :
    IsRow (boundedAboveFlatPerfectSupportedWaldhausen ι)
      ((boundedAboveFlatPerfectSupportedTensorUnitRows ι).obj K) :=
  boundedAboveFlatPerfectSupportedTensorUnitRows_isRow ι K

example :
    IsExact (boundedAboveFlatPerfectSupportedWaldhausen ι).cof
      (boundedAboveFlatPerfectSupportedWaldhausen ι).weq
      (waldhausenStructure (boundedAboveFlatPerfectSupportedWaldhausen ι) ⦋1⦌).cof
      (waldhausenStructure (boundedAboveFlatPerfectSupportedWaldhausen ι) ⦋1⦌).weq
      (boundedAboveFlatPerfectSupportedTensorUnitFirstRow ι) :=
  boundedAboveFlatPerfectSupportedTensorUnitFirstRow_exact ι

example (r : (Γ(X, ⊤))ˣ)
    (K : (boundedAboveFlatPerfectSupported ι).FullSubcategory) :
    ((supportedTensorUnitFirstRowAutomorphism ι r).hom.app K).hom =
      (boundedAboveFlatPerfectSupportedTensorUnitRowsAutomorphism ι r).hom.app K :=
  supportedTensorUnitFirstRowAutomorphism_original ι r K

example (r : (Γ(X, ⊤))ˣ) :
    (supportedTensorUnitFirstRowAutomorphism ι r).hom ≫ (supportedTensorUnitFirstRowIso ι).hom =
      (supportedTensorUnitFirstRowIso ι).hom ≫
        (Functor.isoWhiskerRight (boundedAboveFlatPerfectSupportedTensorUnitAutomorphism ι r)
          (oneEmbedding (boundedAboveFlatPerfectSupportedWaldhausen ι))).hom :=
  supportedTensorUnitFirstRowAutomorphism_comparison ι r

end
end AlgebraicGeometry.Scheme.Modules.SupportedTensorRowTest
