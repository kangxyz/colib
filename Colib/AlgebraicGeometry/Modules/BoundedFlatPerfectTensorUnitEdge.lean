/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectTensorUnitAction
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# The original coefficient edge acting by tensor on complexes

Start with the actual module arrow `μr : O ⟶ O`, apply the genuine tensor coefficient functor,
and only then pass to degreewise tensor on complexes. The resulting functor on `[1]` is proved
equal to the edge of the original tensor automorphism. This records the tensor construction
before applying any nerve, Waldhausen normalization or realization.

Adapted from Quillen at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open Stacks.RegularSequence (globalSmulCenter)
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The native sheaf-of-modules monoidal structure on the scheme. -/
local instance boundedFlatPerfectTensorUnitEdgeMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace
local instance boundedFlatPerfectTensorUnitEdgePreadditive (X : Scheme.{u}) :
    MonoidalPreadditive X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidalPreadditive X.toRingedSpace

/-- The actual sheaf coefficient tensor functor applied degreewise to original complexes.
This does not assert exactness for arbitrary coefficient sheaves. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitEdge.lean:35"
  "adaptation" "Native degreewise tensor and left-unitor comparison"]
def complexTensorCoefficientFunctor (X : Scheme.{u}) :
    X.Modules ⥤ (CochainComplex X.Modules ℤ ⥤ CochainComplex X.Modules ℤ) where
  obj L := (MonoidalCategory.tensorLeft L).mapHomologicalComplex (.up ℤ)
  map f := ((MonoidalCategory.curriedTensor X.Modules).map f).mapHomologicalComplex (.up ℤ)
  map_id L := by
    rw [CategoryTheory.Functor.map_id, NatTrans.mapHomologicalComplex_id]
  map_comp f g := by
    rw [CategoryTheory.Functor.map_comp, NatTrans.mapHomologicalComplex_comp]

/-- The coefficient edge starts with the original module automorphism, before tensoring. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitEdge.lean:46"
  "adaptation" "Native degreewise tensor and left-unitor comparison"]
def complexTensorUnitCoefficientEdge (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    Fin 2 ⥤ (CochainComplex X.Modules ℤ ⥤ CochainComplex X.Modules ℤ) :=
  ComposableArrows.mk₁ (tensorCoefficientUnitIso X r).hom ⋙ complexTensorCoefficientFunctor X

/-- Tensoring the actual coefficient edge produces the original complex tensor automorphism. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitEdge.lean:51"
  "adaptation" "Native degreewise tensor and left-unitor comparison"]
theorem complexTensorUnitCoefficientEdge_eq (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) :
    complexTensorUnitCoefficientEdge X r =
      ComposableArrows.mk₁ (complexTensorUnitAutomorphism X r).hom := by
  apply ComposableArrows.ext₁ (F := complexTensorUnitCoefficientEdge X r)
    (G := ComposableArrows.mk₁ (complexTensorUnitAutomorphism X r).hom) rfl rfl
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- Every crossing arrow is the original module coefficient tensor in each complex degree. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitEdge.lean:60"
  "adaptation" "Native degreewise tensor and left-unitor comparison"]
theorem complexTensorUnitCoefficientEdge_crossing_f (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ)
    (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    (((complexTensorUnitCoefficientEdge X r).map (homOfLE (show (0 : Fin 2) ≤ 1 by decide))).app
      K).f n = ((MonoidalCategory.curriedTensor X.Modules).map (tensorCoefficientUnitIso X
      r).hom).app (K.X n) := rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0542"] complexTensorUnitCoefficientEdge_crossing_f

end AlgebraicGeometry.Scheme.Modules
