/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectScalarCofiber
public import Colib.KTheory.Waldhausen.Fibration.CofiberPrismFiber

/-!
# The original scalar-cofiber prism after open restriction

The actual scalar factorization has a fine weak projection. The original scalar is coarse weak
because its restriction is the specified global unit, so two-out-of-three proves that the actual
cofibration factor is coarse weak. Its original quotient square therefore supplies the previously
constructed continuous cofiber prism and canonical-fiber face. The source scalar need not be a unit.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberPrism.lean:96-130`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native perfect complexes retain
ambient monomorphism cofibrations, quasi-isomorphisms, and the actual signed cone.
The original maps, path coordinates, basepoints, and signs are unchanged. -/

@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology HomotopyGroup unitInterval
open scoped Topology
open CategoryTheory.Waldhausen.Fibration
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The actual scalar factorization supplies the full original three-parameter cofiber cube. -/
def perfectOpenScalarCofiberCompositionCube (K : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    C(unitInterval × (unitInterval × unitInterval), (perfectOpenNested j).coarse.Delooping) :=
  (perfectOpenNested j).coarse.cofiberPrismCompositionCube (perfectScalarInclusion X r K)
    ((ExtensionCategory.quotient (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).app
      (perfectScalarExtension X r K))
    (perfectScalarInclusion_openCof r j K) (perfectScalarInclusion_openWeak r j q hq K)
    (perfectScalarCofiber_isPushout r j K)

/-- Its comparison-zero face is the original source prefix and original categorical-cofiber fiber.
-/
theorem perfectOpenScalarCofiberCompositionCube_zero (K : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) (t s : unitInterval) :
    perfectOpenScalarCofiberCompositionCube j r q hq K (0, unitInterval.symm s, t) =
      if h : (t : ℝ) ≤ 1 / 2 then
        (perfectOpenNested j).coarse.kZeroObjectLoop K
          ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
      else
        (canonicalFiberObjectLoop (perfectOpenNested j) (perfectOpenScalarCofiberAcyclic r j q hq K)
          ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩).val.2 s :=
  cofiberPrismCompositionCube_zero_fiber (perfectOpenNested j) (perfectScalarInclusion X r K)
    ((ExtensionCategory.quotient (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).app
      (perfectScalarExtension X r K))
    (perfectScalarInclusion_openCof r j K) (perfectScalarInclusion_openWeak r j q hq K)
    (perfectScalarCofiber_isPushout r j K) t s

/-- The same specified family is a jointly continuous square of original based loops. -/
def perfectOpenScalarCofiberCompositionLoops (K : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    C(unitInterval × unitInterval,
      Path (perfectOpenNested j).coarse.kBasepoint (perfectOpenNested j).coarse.kBasepoint) :=
  (perfectOpenNested j).coarse.cofiberPrismCompositionLoops (perfectScalarInclusion X r K)
    ((ExtensionCategory.quotient (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).app
      (perfectScalarExtension X r K))
    (perfectScalarInclusion_openCof r j K) (perfectScalarInclusion_openWeak r j q hq K)
    (perfectScalarCofiber_isPushout r j K)

/-- Every original comparison, nerve and object-loop coordinate is unchanged. -/
theorem perfectOpenScalarCofiberCompositionLoops_apply (K : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) (a s t : unitInterval) :
    perfectOpenScalarCofiberCompositionLoops j r q hq K (a, s) t =
      perfectOpenScalarCofiberCompositionCube j r q hq K (a, s, t) := rfl

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberPrism.lean:96-130" "adaptation"
  "The actual three-parameter cofiber cube, reversed zero face, and original based-loop family on
    native perfect complexes"]
  perfectOpenScalarCofiberCompositionCube perfectOpenScalarCofiberCompositionCube_zero
    perfectOpenScalarCofiberCompositionLoops_apply

end AlgebraicGeometry.Scheme.Modules
