/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectJoint
public import Colib.AlgebraicGeometry.Modules.PerfectSupportedCone

/-!
# Actual joint cylinders with prescribed support

The supported category retains native Stacks perfectness and ambient monomorphisms.
Exact open restriction proves extension and cone closure on the actual complexes.
This supplies genuine cylinder data for any nested weak class on this category.
Implementation provenance: Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/
Support/Cone.lean at c561118b7795eb9780be9ed391c3251d6a4d0afd.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open Waldhausen Fibration
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The chosen ambient zero satisfies the original support predicate. -/
instance perfectSupported_containsZero : (perfectSupported j).ContainsZero where
  exists_zero := ⟨(complexes X.Modules).zero, (complexes X.Modules).isZero,
    (perfectSupported_cofibrationClosed j).zero_mem⟩

/-- Support is invariant under actual chain isomorphisms. -/
instance perfectSupported_closedUnderIsomorphisms :
    (perfectSupported j).IsClosedUnderIsomorphisms where
  of_iso e h := by
    refine ⟨h.1.of_quasiIso e.hom (quasiIso_of_isIso e.hom), ?_⟩
    let e' := ((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso e
    exact fun n => (exactAt_iff_of_quasiIsoAt e'.hom n).1 (h.2 n)

/-- Exact restriction preserves extensions of complexes with the prescribed support. -/
instance perfectSupported_extensionClosed :
    (abelianExactStructure (CochainComplex X.Modules ℤ)).IsExtensionClosed
      (perfectSupported j) where
  prop_middle hS h₁ h₃ :=
    ⟨RingedSpace.isPerfectComplex_X₂_of_shortExact X.toRingedSpace hS h₁.1 h₃.1,
      (hS.map_of_exact ((restrictFunctor j).mapHomologicalComplex
        (ComplexShape.up ℤ))).acyclic_X₂ h₁.2 h₃.2⟩

/-- Finite products of the actual supported complexes remain supported. -/
instance perfectSupported_closedUnderFiniteProducts :
    (perfectSupported j).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (CochainComplex X.Modules ℤ)).extensionClosed_finiteProducts
    (perfectSupported j)

/-- The actual mapping cone retains prescribed support. -/
theorem perfectSupported_coneClosed {K L : CochainComplex X.Modules ℤ}
    (hK : perfectSupported j K) (hL : perfectSupported j L) (f : K ⟶ L) :
    perfectSupported j (CochainComplex.mappingCone f) := by
  apply perfectSupported_mappingCone j f hK.1 hL.1
  rw [quasiIso_iff]
  intro n
  exact (quasiIsoAt_iff_exactAt _ n (hK.2 n)).2 (hL.2 n)

/-- Genuine ambient-monomorphism joint data for arbitrary nested weak equivalences. -/
def perfectSupportedJointData (N : NestedWeakEquivalences (perfectSupportedWaldhausen j)) :
    RowFactorization.JointData N :=
  cofibrationClosedComplexJointData (perfectSupported j) (perfectSupported_cofibrationClosed j)
    (perfectSupported_coneClosed j) N

/-- The actual second endpoint retracts the actual cylinder projection. -/
theorem perfectSupportedJointData_secondEndpointSection
    (N : NestedWeakEquivalences (perfectSupportedWaldhausen j)) :
    RowFactorization.SecondEndpointSection N (perfectSupportedJointData j N) :=
  cofibrationClosedComplexJointData_secondEndpointSection (perfectSupported j)
    (perfectSupported_cofibrationClosed j) (perfectSupported_coneClosed j) N

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Support/Cone.lean:29-43"
    "adaptation" "Native perfect and acyclic cone closure for the actual supported cylinder"]
  AlgebraicGeometry.Scheme.Modules.perfectSupported_coneClosed
