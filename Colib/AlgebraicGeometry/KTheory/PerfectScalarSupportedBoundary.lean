/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarForwardRelativeBoundary
public import Colib.AlgebraicGeometry.KTheory.PerfectOpenLongExactSequence
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarKOne

/-!
# The original relative scalar boundary in supported K-zero

The existing relative scalar boundary transports through the actual acyclic-to-supported
functor. Its value is the literal signed scalar cone object class. Only an open immersion is
required. No fine-open localization, Laurent, Bass, or all-degree scalar formula is asserted.
-/

/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarSupportedBoundary.lean:35-48`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native perfect complexes retain
ambient monomorphism cofibrations, quasi-isomorphisms, and the actual signed cone.
The original maps, path coordinates, basepoints, and signs are unchanged. -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology HomotopyGroup TopologicalSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original relative supported boundary is the actual scalar mapping-cone object class. -/
theorem perfectOpenConnectingHom_scalarForward {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (K : ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
    (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q) :
    perfectOpenConnectingHom j 0 (perfectScalarForwardKOneClass j K r q hq) =
      (perfectSupportedWaldhausen j).kZeroObjectClass
        ((perfectAcyclicToSupported j).obj (perfectOpenScalarCone r j q hq K)) := by
  change (perfectAcyclicSupportedKEquiv j 0)
    (changeWeakConnectingHom (perfectOpenNested j)
      (perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j) 0
      (perfectScalarForwardKOneClass j K r q hq)) = _
  rw [perfectScalarForward_changeWeakBoundary,
    (acyclicStructure (perfectOpenNested j)).kZeroObjectClass_iso
      (perfectOpenScalarCofiberAcyclicIso r j q hq K)]
  exact KMap_kZeroObjectClass (perfectAcyclicToSupported_exact j)
    (perfectOpenScalarCone r j q hq K)

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarSupportedBoundary.lean:35-48" "adaptation"
  "For any open immersion and native perfect complex, the original relative connecting homomorphism
    sends the independent forward scalar class to the actual positive supported signed cone class"]
  perfectOpenConnectingHom_scalarForward

attribute [colib_tag "COL-0304"] perfectOpenConnectingHom_scalarForward

end AlgebraicGeometry.Scheme.Modules
