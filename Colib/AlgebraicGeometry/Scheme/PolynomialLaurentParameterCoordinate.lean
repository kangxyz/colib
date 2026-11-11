/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentIndexSquare
public import Colib.AlgebraicGeometry.Scheme.LaurentCoordinateNaturality

/-!
# The original Laurent coordinate at every scheme parameter

The coordinate is pulled through the actual second product projection. This is the two-declaration
geometric prerequisite from `GlobalSchemeLaurentTrack.lean`, not the realized track or seed square.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Products
universe u
namespace AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex

/-- The original forward Laurent coordinate on the actual product with any scheme. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSchemeLaurentTrack.lean:41"
  "adaptation" "The original Laurent coordinate, actual projections and unchanged scalar action."]
def laurentScalar (X : Scheme.{u}ᵒᵖ) : (Γ((laurent.op.obj X).unop, ⊤))ˣ :=
  Units.map (pullback.snd (specULiftZIsTerminal.from X.unop)
    (laurentProjection (.of (ULift.{u} ℤ)))).appTop.hom.toMonoidHom
      (laurentCoordinate (.of (ULift.{u} ℤ)))

/-- Every original scheme map keeps the same forward coordinate under actual pullback. -/
@[colib_ref "quillen" "Quillen c561118b: GlobalSchemeLaurentTrack.lean:47"
  "adaptation" "The original Laurent coordinate, actual projections and unchanged scalar action."]
theorem laurentScalar_map {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    Units.map (laurent.op.map f).unop.appTop.hom.toMonoidHom (laurentScalar X) =
      laurentScalar Y := by
  apply Units.ext
  have h : laurent.map f.unop ≫
      pullback.snd (specULiftZIsTerminal.from X.unop) (laurentProjection (.of (ULift.{u} ℤ))) =
      pullback.snd (specULiftZIsTerminal.from Y.unop) (laurentProjection (.of (ULift.{u} ℤ))) := by
    simp [laurent, baseProductFunctor]
  have hs := congrArg (fun g => g.appTop) h
  rw [Scheme.Hom.comp_appTop] at hs
  exact ConcreteCategory.congr_hom hs (↑(laurentCoordinate (.of (ULift.{u} ℤ))))

end AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
