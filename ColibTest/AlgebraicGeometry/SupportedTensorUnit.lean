/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportHomotopy
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules.SupportedTensorUnitTest
noncomputable section
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

example
    (r : (Γ(X, ⊤))ˣ) (K : (boundedAboveFlatPerfectSupported j).FullSubcategory) :
    (boundedAboveFlatPerfectSupported j).ι.map
        ((boundedAboveFlatPerfectSupportedTensorUnitAutomorphism j r).hom.app K) =
      (complexTensorUnitAutomorphism X r).hom.app K.obj :=
  boundedAboveFlatPerfectSupportedTensorUnitAutomorphism_hom_original j r K

example (r : (Γ(X, ⊤))ˣ) :
    (boundedAboveFlatPerfectSupportedTensorUnitAutomorphism j r).hom ≫
        (boundedAboveFlatPerfectSupportedTensorUnitIso j).hom =
      (boundedAboveFlatPerfectSupportedTensorUnitIso j).hom ≫
        (boundedAboveFlatPerfectSupportedGlobalUnitIso j r).hom :=
  boundedAboveFlatPerfectSupportedTensorUnitAutomorphism_unitor j r

example :
    CategoryTheory.Waldhausen.IsExact (boundedAboveFlatPerfectSupportedWaldhausen j).cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).weq
      (boundedAboveFlatPerfectSupportedWaldhausen j).cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).weq
      (boundedAboveFlatPerfectSupportedTensorUnit j) :=
  boundedAboveFlatPerfectSupportedTensorUnit_exact j

example (r : (Γ(X, ⊤))ˣ) :
    (boundedAboveFlatPerfectSupportedTensorUnitAutomorphism j r).hom.app
        (boundedAboveFlatPerfectSupportedWaldhausen j).zero = 𝟙 _ :=
  boundedAboveFlatPerfectSupportedTensorUnitAutomorphism_zero j r

example (r : (Γ(X, ⊤))ˣ) :
    ((boundedAboveFlatPerfectSupportedTensorUnitHomotopy j r).trans
      (boundedAboveFlatPerfectSupportedTensorUnitUnitorHomotopy j)).RelHomotopy
      ((boundedAboveFlatPerfectSupportedTensorUnitUnitorHomotopy j).trans
        (boundedAboveFlatPerfectSupportedGlobalUnitHomotopy j r)) :=
  boundedAboveFlatPerfectSupportedTensorUnitUnitorPasting j r

end
end AlgebraicGeometry.Scheme.Modules.SupportedTensorUnitTest
