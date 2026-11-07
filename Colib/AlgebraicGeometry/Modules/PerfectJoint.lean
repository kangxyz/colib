/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectWaldhausen
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.CofibrationClosedComplexJoint

/-! # The actual joint cylinder on native perfect complexes

Native Stacks perfectness supplies zero, isomorphism, extension and cone closure.
The ambient exact structure below records an object-closure property only. The
joint data use the existing `perfectComplexesWaldhausen`, whose cofibrations are
literal ambient monomorphisms. No auxiliary local-perfect model is introduced.
Source-only draft; no compilation claim.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry StrictlyPerfect
open CategoryTheory.ExactCategory
open scoped ZeroObject
namespace AlgebraicGeometry.RingedSpace
universe u
variable (X : RingedSpace.{u, u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The chosen ambient zero belongs to the native perfect predicate. -/
instance isPerfectComplex_containsZero :
    (IsPerfectComplex (X := X)).ContainsZero where
  exists_zero := ⟨(Waldhausen.complexes (OXMod.{u, u, u} X)).zero,
    (Waldhausen.complexes (OXMod.{u, u, u} X)).isZero,
    (perfectComplexes_cofibrationClosed X).zero_mem⟩

/-- Actual chain isomorphisms preserve native Stacks perfectness. -/
instance isPerfectComplex_closedUnderIsomorphisms :
    (IsPerfectComplex (X := X)).IsClosedUnderIsomorphisms where
  of_iso e h := h.of_quasiIso e.hom (quasiIso_of_isIso e.hom)

/-- Native perfectness is closed under actual short exact extensions. -/
theorem isPerfectComplex_X₂_of_shortExact
    {S : ShortComplex (CochainComplex (OXMod.{u, u, u} X) ℤ)} (hS : S.ShortExact)
    (h₁ : IsPerfectComplex S.X₁) (h₃ : IsPerfectComplex S.X₃) :
    IsPerfectComplex S.X₂ := by
  let : HasDerivedCategory.{u + 1} (OXMod.{u, u, u} X) := HasDerivedCategory.standard _
  have h : IsPerfect (DerivedCategory.Q.obj S.X₂) :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₂_of_distinguished
      (DerivedCategory.triangleOfSES hS) (DerivedCategory.triangleOfSES_distinguished hS)
      h₁.isPerfect h₃.isPerfect
  exact isPerfectComplex_of_isPerfect_representation h ⟨Iso.refl _⟩

/-- This records object closure only; it does not select a Waldhausen structure. -/
instance isPerfectComplex_extensionClosed :
    (abelianExactStructure (CochainComplex (OXMod.{u, u, u} X) ℤ)).IsExtensionClosed
      (IsPerfectComplex (X := X)) where
  prop_middle hS h₁ h₃ := isPerfectComplex_X₂_of_shortExact X hS h₁ h₃

/-- The actual finite products are perfect, by the preceding native closure facts. -/
instance isPerfectComplex_closedUnderFiniteProducts :
    (IsPerfectComplex (X := X)).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (CochainComplex (OXMod.{u, u, u} X) ℤ)).extensionClosed_finiteProducts
    (IsPerfectComplex (X := X))

/-- The native cone-closure certificate with the argument order of the pure cylinder. -/
theorem perfectComplexes_coneClosed
    {K L : CochainComplex (OXMod.{u, u, u} X) ℤ}
    (hK : IsPerfectComplex K) (hL : IsPerfectComplex L) (f : K ⟶ L) :
    IsPerfectComplex (CochainComplex.mappingCone f) :=
  isPerfectComplex_mappingCone f hK hL

/-- Actual joint data on the existing native perfect category, for any nested weak class. -/
def perfectComplexesJointData
    (N : Waldhausen.Fibration.NestedWeakEquivalences (perfectComplexesWaldhausen X)) :
    Waldhausen.Fibration.RowFactorization.JointData N :=
  Waldhausen.Fibration.cofibrationClosedComplexJointData (IsPerfectComplex (X := X))
    (perfectComplexes_cofibrationClosed X) (perfectComplexes_coneClosed X) N

/-- The unchanged target endpoint retracts the unchanged perfect cylinder projection. -/
theorem perfectComplexesJointData_secondEndpointSection
    (N : Waldhausen.Fibration.NestedWeakEquivalences (perfectComplexesWaldhausen X)) :
    Waldhausen.Fibration.RowFactorization.SecondEndpointSection N
      (perfectComplexesJointData X N) :=
  Waldhausen.Fibration.cofibrationClosedComplexJointData_secondEndpointSection
    (IsPerfectComplex (X := X)) (perfectComplexes_cofibrationClosed X)
    (perfectComplexes_coneClosed X) N

end AlgebraicGeometry.RingedSpace
