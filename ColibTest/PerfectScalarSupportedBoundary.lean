/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.PerfectScalarSupportedBoundary

/-! Native scalar boundary regressions: arbitrary opens, original signed cone, and both signs. -/

noncomputable section
open CategoryTheory Waldhausen Fibration AlgebraicGeometry Topology
open AlgebraicGeometry.Scheme.Modules
open scoped Topology
universe u v

section Scalar
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

-- The input class is defined independently by the actual forward scalar weak arrow.
example : perfectScalarForwardKOneClass j K r q hq =
    (perfectOpenNested j).coarse.weakEndomorphismKOneClass ((perfectGlobalScalar X r).app K)
      (quasiIso_restrict_complexGlobalScalar j r q hq K.obj) := rfl

-- The path produced by the actual cofiber is inverse before the transpose sign cancels it.
example : perfectScalarCofiberBoundaryKOneClass j K r q hq =
    (perfectScalarForwardKOneClass j K r q hq)⁻¹ :=
  perfectScalarCofiberBoundaryKOneClass_eq_inv j K r q hq

-- The original relative boundary is positive on the original supported cone object class.
example : perfectOpenConnectingHom j 0 (perfectScalarForwardKOneClass j K r q hq) =
    (perfectSupportedWaldhausen j).kZeroObjectClass
      ((perfectAcyclicToSupported j).obj (perfectOpenScalarCone r j q hq K)) :=
  perfectOpenConnectingHom_scalarForward j K r q hq

-- The supported object is literally Mathlib's signed mapping cone, not a replacement class.
example : (((perfectAcyclicToSupported j).obj (perfectOpenScalarCone r j q hq K))).obj =
    CochainComplex.mappingCone ((complexGlobalScalar X r).app K.obj) := rfl

-- Equivalently, the endpoint uses the existing direct supported scalar-cone functor.
example : perfectOpenConnectingHom j 0 (perfectScalarForwardKOneClass j K r q hq) =
    (perfectSupportedWaldhausen j).kZeroObjectClass
      ((perfectSupportedScalarConeFunctor j r q hq).obj K) :=
  perfectOpenConnectingHom_scalarForward j K r q hq

-- The canonical cofiber comparison retains the signed quotient map itself.
example :
    (ExtensionCategory.quotient (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).app
        (perfectScalarExtension X r K) ≫ (perfectOpenScalarCofiberIso r j q hq K).hom =
      ObjectProperty.homMk
        (CochainComplex.SplitFactorization.quotientToCone ((complexGlobalScalar X r).app K.obj)) :=
  perfectOpenScalarCofiberIso_quotient r j q hq K

end Scalar

section GenericUniverses
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (A : AcyclicCategory N)

-- Object and morphism universes remain independent at the actual canonical-fiber interface.
example : canonicalFiberKMap N 0 ((acyclicStructure N).kZeroObjectClass A) =
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      (FundamentalGroup.fromPath ⟦canonicalFiberObjectLoop N A⟧) :=
  canonicalFiberKMap_object N A

end GenericUniverses
