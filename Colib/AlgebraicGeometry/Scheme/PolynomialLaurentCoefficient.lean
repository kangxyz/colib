/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentIndexSquare

/-! # The original coefficient projection on the scheme Laurent index -/
@[expose] public noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex

/-- The unchanged opposite of the actual Laurent projection. -/
@[colib_ref "quillen" "Quillen c561118b: GeometricSeedCospan.lean:38"
  "adaptation" "The original projection; no seed cospan or whole-unit-square assertion."]
def coefficient : 𝟭 Scheme.{u}ᵒᵖ ⟶ laurent.op :=
  NatTrans.op (baseProductProjection (laurentProjection (.of (ULift.{u} ℤ))))

end AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
