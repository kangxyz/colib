/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.ExtensionByZeroExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Extension by zero of complexes of module sheaves

Apply the genuine extension-by-zero functor degreewise. The chain adjunction has exactly
its module-sheaf unit and counit in every degree. Exactness of extension by zero gives
preservation of quasi-isomorphisms; no perfectness or finiteness assumption is imposed.

Adapted from `Quillen/Aglib/AlgebraicGeometry/Modules/Complex/ExtensionByZero.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`, using native Mathlib module sheaves
and the native extension-by-zero construction in Colib.
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory Limits HomologicalComplex

namespace AlgebraicGeometry.Scheme.Modules.Complex

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Extension by zero in every degree of a complex of module sheaves. -/
def extensionByZero : CochainComplex U.Modules ℤ ⥤ CochainComplex X.Modules ℤ :=
  (Modules.extensionByZero j).mapHomologicalComplex (.up ℤ)

instance : (extensionByZero j).Additive := by
  unfold extensionByZero
  infer_instance

/-- The chain-level adjunction to actual termwise open restriction. -/
def extensionByZeroAdjunction :
    extensionByZero j ⊣ (restrictFunctor j).mapHomologicalComplex (.up ℤ) where
  unit := {
    app K := {
      f n := (extensionByZeroRestrictAdjunction j).unit.app (K.X n)
      comm' p q _ := ((extensionByZeroRestrictAdjunction j).unit.naturality (K.d p q)).symm }
    naturality {K L} f := by
      ext n : 1
      exact (extensionByZeroRestrictAdjunction j).unit.naturality (f.f n) }
  counit := {
    app K := {
      f n := (extensionByZeroRestrictAdjunction j).counit.app (K.X n)
      comm' p q _ := ((extensionByZeroRestrictAdjunction j).counit.naturality (K.d p q)).symm }
    naturality {K L} f := by
      ext n : 1
      exact (extensionByZeroRestrictAdjunction j).counit.naturality (f.f n) }
  left_triangle_components K := by
    ext n : 1
    exact (extensionByZeroRestrictAdjunction j).left_triangle_components (K.X n)
  right_triangle_components K := by
    ext n : 1
    exact (extensionByZeroRestrictAdjunction j).right_triangle_components (K.X n)

instance : (extensionByZero j).IsLeftAdjoint :=
  (extensionByZeroAdjunction j).isLeftAdjoint

instance extensionByZero_unit_app_isIso (K : CochainComplex U.Modules ℤ) :
    IsIso ((extensionByZeroAdjunction j).unit.app K) := by
  let : ∀ n, IsIso (((extensionByZeroAdjunction j).unit.app K).f n) := fun n =>
    inferInstanceAs (IsIso ((extensionByZeroRestrictAdjunction j).unit.app (K.X n)))
  exact HomologicalComplex.Hom.isIso_of_components _

instance extensionByZero_unit_isIso : IsIso (extensionByZeroAdjunction j).unit :=
  NatIso.isIso_of_isIso_app _

/-- Restricting the extended complex recovers the original complex. -/
def extensionByZeroRestrictIso :
    extensionByZero j ⋙ (restrictFunctor j).mapHomologicalComplex (.up ℤ) ≅
      𝟭 (CochainComplex U.Modules ℤ) :=
  (asIso (extensionByZeroAdjunction j).unit).symm

instance : PreservesColimitsOfSize.{v, w} (extensionByZero j) :=
  (extensionByZeroAdjunction j).leftAdjoint_preservesColimits

instance : PreservesFiniteLimits (extensionByZero j) := by
  unfold extensionByZero
  infer_instance

/-- Exact extension by zero preserves quasi-isomorphisms of module-sheaf complexes. -/
instance extensionByZero_quasiIso {K L : CochainComplex U.Modules ℤ} (f : K ⟶ L)
    [QuasiIso f] : QuasiIso ((extensionByZero j).map f) := by
  unfold extensionByZero
  infer_instance

/-- Restriction of the actual counit is an isomorphism of complexes. -/
instance restrict_extensionByZero_counit_isIso (K : CochainComplex X.Modules ℤ) :
    IsIso (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map
      ((extensionByZeroAdjunction j).counit.app K)) :=
  isIso_of_hom_comp_eq_id _ ((extensionByZeroAdjunction j).right_triangle_components K)

end AlgebraicGeometry.Scheme.Modules.Complex
