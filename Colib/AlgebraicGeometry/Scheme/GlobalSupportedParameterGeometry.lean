/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.Scheme.IntegerBaseProducts
public import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.Basic

/-!
# The actual integer-base open pair at every scheme parameter

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/`
`GlobalSupportedParameterGeometry.lean` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original two product projections and commuting squares use the native category of open
immersions. No compactness, flatness or cartesianness assumption is added.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
universe u
namespace AlgebraicGeometry.Scheme.GlobalSupportedParameter

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The original product open immersion, with the parameter as its first factor. -/
@[colib_ref "quillen"
  "Quillen c561118b: GlobalSupportedParameterGeometry.lean:22"
  "adaptation" "The original product-pair maps on native scheme and arrow objects."]
def openTransformation :
    baseProductFunctor (specULiftZIsTerminal.from P) ⟶
      baseProductFunctor (specULiftZIsTerminal.from Q) :=
  baseProductTransformation _ _ f (specULiftZIsTerminal.hom_ext _ _)

/-- At a genuine scheme parameter the original open arrow defines an open pair. -/
@[colib_ref "quillen"
  "Quillen c561118b: GlobalSupportedParameterGeometry.lean:27"
  "adaptation" "The original product-pair maps on native scheme and arrow objects."]
def pair (S : Scheme.{u}) : Scheme.OpenPairs.{u} :=
  MorphismProperty.Arrow.mk ((openTransformation f).app S) (by
    change IsOpenImmersion ((baseProductTransformation (specULiftZIsTerminal.from P)
      (specULiftZIsTerminal.from Q) f (specULiftZIsTerminal.hom_ext _ _)).app S)
    infer_instance)

/-- The full commutative square induced by an arbitrary parameter map. -/
@[colib_ref "quillen"
  "Quillen c561118b: GlobalSupportedParameterGeometry.lean:34"
  "adaptation" "The original product-pair maps on native scheme and arrow objects."]
def pairMap {S T : Scheme.{u}} (g : S ⟶ T) : pair f S ⟶ pair f T :=
  MorphismProperty.Arrow.homMk
    ((baseProductFunctor (specULiftZIsTerminal.from P)).map g)
    ((baseProductFunctor (specULiftZIsTerminal.from Q)).map g)
    ((openTransformation f).naturality g)

/-- Actual product pairs form a strict covariant diagram; supported pullback is contravariant. -/
@[colib_ref "quillen"
  "Quillen c561118b: GlobalSupportedParameterGeometry.lean:41"
  "adaptation" "The original product-pair maps on native scheme and arrow objects."]
def pairs : Scheme.{u} ⥤ Scheme.OpenPairs.{u} where
  obj := pair f
  map := pairMap f
  map_id S := by
    apply MorphismProperty.Arrow.Hom.ext
    · exact (baseProductFunctor (specULiftZIsTerminal.from P)).map_id S
    · exact (baseProductFunctor (specULiftZIsTerminal.from Q)).map_id S
  map_comp g h := by
    apply MorphismProperty.Arrow.Hom.ext
    · exact (baseProductFunctor (specULiftZIsTerminal.from P)).map_comp g h
    · exact (baseProductFunctor (specULiftZIsTerminal.from Q)).map_comp g h

/-- The ambient side is the unchanged product functor map. -/
@[colib_ref "quillen"
  "Quillen c561118b: GlobalSupportedParameterGeometry.lean:56"
  "adaptation" "The original product-pair maps on native scheme and arrow objects."]
theorem pairMap_right {S T : Scheme.{u}} (g : S ⟶ T) :
    (pairMap f g).right = (baseProductFunctor (specULiftZIsTerminal.from Q)).map g := rfl

/-- The open side is the unchanged product functor map. -/
@[colib_ref "quillen"
  "Quillen c561118b: GlobalSupportedParameterGeometry.lean:60"
  "adaptation" "The original product-pair maps on native scheme and arrow objects."]
theorem pairMap_left {S T : Scheme.{u}} (g : S ⟶ T) :
    (pairMap f g).left = (baseProductFunctor (specULiftZIsTerminal.from P)).map g := rfl

end AlgebraicGeometry.Scheme.GlobalSupportedParameter


namespace AlgebraicGeometry.Scheme.GlobalSupportedParameter

attribute [colib_tag "COL-0536"] pairs

end AlgebraicGeometry.Scheme.GlobalSupportedParameter
