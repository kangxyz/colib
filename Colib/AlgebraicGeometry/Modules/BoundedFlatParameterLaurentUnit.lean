/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentParameterCoordinate
public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSectionUnit

/-!
# The original Laurent unit for scheme-parameter product families

The parameter coordinate on `(S × L) × Q` is pulled from `S × L`, and hence from
its original Laurent factor. Both parameter maps and maps of the fixed factor
preserve that exact unit. All products are over the integral terminal scheme.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Functor.IdentityAutomorphism
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterLaurentUnit

private theorem pullbackUnit_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (v : (Γ(Z, ⊤))ˣ) :
    Units.map f.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom v) =
      Units.map (f ≫ g).appTop.hom.toMonoidHom v := by
  ext
  simp

/-- The original parameter Laurent coordinate, pulled through the fixed-factor projection. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentUnit.lean:37"
  "adaptation" "The original Laurent coordinate, actual projections and unchanged scalar action."]
def projectedLaurentScalar (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (Γ(((baseProductFunctor (specULiftZIsTerminal.from Q)).op.obj
      (laurent.op.obj X)).unop, ⊤))ˣ :=
  Units.map ((baseProductProjection (specULiftZIsTerminal.from Q)).app
    (laurent.op.obj X).unop).appTop.hom.toMonoidHom (laurentScalar X)

/-- Every actual parameter scheme map preserves the projected original Laurent coordinate. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentUnit.lean:43"
  "adaptation" "The original Laurent coordinate, actual projections and unchanged scalar action."]
theorem projectedLaurentScalar_map (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ}
    (g : X ⟶ Y) :
    Units.map (((baseProductFunctor (specULiftZIsTerminal.from Q)).op.map
      (laurent.op.map g)).unop).appTop.hom.toMonoidHom (projectedLaurentScalar Q X) =
      projectedLaurentScalar Q Y := by
  change Units.map ((baseProductFunctor (specULiftZIsTerminal.from Q)).map
    (laurent.map g.unop)).appTop.hom.toMonoidHom
      (Units.map ((baseProductProjection (specULiftZIsTerminal.from Q)).app
        (laurent.obj X.unop)).appTop.hom.toMonoidHom (laurentScalar X)) = _
  rw [pullbackUnit_comp, (baseProductProjection (specULiftZIsTerminal.from Q)).naturality]
  rw [← pullbackUnit_comp]
  exact congrArg (Units.map ((baseProductProjection (specULiftZIsTerminal.from Q)).app
    (laurent.obj Y.unop)).appTop.hom.toMonoidHom) (laurentScalar_map g)

/-- A map of the fixed factor preserves the parameter coordinate, including open restriction. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentUnit.lean:58"
  "adaptation" "The original Laurent coordinate, actual projections and unchanged scalar action."]
theorem projectedLaurentScalar_factor {P Q : Scheme.{u}} (f : P ⟶ Q)
    (X : Scheme.{u}ᵒᵖ) :
    Units.map ((baseProductTransformation (specULiftZIsTerminal.from P)
      (specULiftZIsTerminal.from Q)
      f (specULiftZIsTerminal.hom_ext _ _)).app (laurent.op.obj X).unop).appTop.hom.toMonoidHom
        (projectedLaurentScalar Q X) = projectedLaurentScalar P X := by
  unfold projectedLaurentScalar
  rw [pullbackUnit_comp, baseProductTransformation_projection]

/-- The actual evaluation-lifted identity unit on the native parameter ambient section category. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentUnit.lean:67"
  "adaptation" "The original Laurent coordinate, actual projections and unchanged scalar action."]
def ambientUnit (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    𝟭 (BoundedAboveFlatGlobalSections ((baseProductFunctor (specULiftZIsTerminal.from
      Q)).op.obj (laurent.op.obj X))) ≅
      𝟭 (BoundedAboveFlatGlobalSections ((baseProductFunctor (specULiftZIsTerminal.from
        Q)).op.obj (laurent.op.obj X))) :=
  boundedAboveFlatGlobalSectionUnit _ (projectedLaurentScalar Q X)

/-- Original global reindexing preserves this same parameter unit for every scheme arrow. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentUnit.lean:73"
  "adaptation" "The original Laurent coordinate, actual projections and unchanged scalar action."]
theorem ambientUnit_naturality (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    Preserves (boundedAboveFlatGlobalSectionsMap
      ((baseProductFunctor (specULiftZIsTerminal.from Q)).op.map (laurent.op.map g)))
        (ambientUnit Q X) (ambientUnit Q Y) :=
  boundedAboveFlatGlobalSectionUnit_reindex_of_eq _ _ _ (projectedLaurentScalar_map Q g)

/-- Actual pullback along the fixed-factor map preserves the original parameter unit. -/
@[colib_ref "quillen" "Quillen c561118b: ParameterLaurentUnit.lean:79"
  "adaptation" "The original Laurent coordinate, actual projections and unchanged scalar action."]
theorem ambientUnit_factor {P Q : Scheme.{u}} (f : P ⟶ Q) (X : Scheme.{u}ᵒᵖ) :
    Preserves (boundedAboveFlatGlobalSectionsMap
      (((baseProductTransformation (specULiftZIsTerminal.from P)
        (specULiftZIsTerminal.from Q) f (specULiftZIsTerminal.hom_ext _ _)).app
          (laurent.op.obj X).unop).op)) (ambientUnit Q X) (ambientUnit P X) :=
  boundedAboveFlatGlobalSectionUnit_reindex_of_eq _ _ _ (projectedLaurentScalar_factor f X)

end AlgebraicGeometry.Scheme.Modules.ParameterLaurentUnit

namespace AlgebraicGeometry.Scheme.Modules.ParameterLaurentUnit

attribute [colib_tag "COL-0537"] ambientUnit
attribute [colib_tag "COL-0537"] ambientUnit_naturality
attribute [colib_tag "COL-0537"] ambientUnit_factor

end AlgebraicGeometry.Scheme.Modules.ParameterLaurentUnit
