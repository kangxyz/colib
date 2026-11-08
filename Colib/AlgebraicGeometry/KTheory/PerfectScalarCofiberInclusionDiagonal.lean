/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberPrespectrumTrack
public import Colib.KTheory.Waldhausen.Additivity.EndpointTransformationSquare
public import Colib.Topology.Realization.HomotopySquare

/-!
# The whole original scalar inclusion diagonal cylinder

The scalar additivity square's actual normalized inclusion cylinder agrees through the original
bisimplicial diagonal isomorphisms with its ordinary weak-transformation cylinder. The identity
retains every simplicial input, and its realization retains the full original time and source.
It uses the same canonical endpoint rebases as the scalar inclusion/projection sequence.
-/
/-! Implementation provenance:
    `Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarCofiberInclusionDiagonal.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole tracks, signs and
    independent parameters are retained. -/
@[expose] public section
open Topology SSet CategoryTheory.Functor

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
    CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.Additivity Topology.LoopPrespectrum
open scoped Topology Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)
local notation "hF" => changeWeak_exact (perfectOpenNested j)
local notation "hM" =>
  Additivity.IsCofibrationSequence.exactG (perfectOpenScalarCofibrationSequence j r)

/-- The exact normalized inclusion edge of the scalar additivity square, before realization. -/
theorem perfectOpenScalarInclusionDiagonalCylinder :
    (normalizedMiddleTransformationHomotopy V W
      (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
    X.toRingedSpace))))) (perfectScalarInclusionNat X r)
      (QuotientRows.oneIdToZero W) (perfectScalarConeProjectionNat X r)
      (perfectOpenScalarIdentityCofibrationSequence j) (perfectOpenScalarCofibrationSequence j r)
      (perfectScalarInclusionNat X r) (perfectScalarInclusionNat_openWeak j r q hq)).h ≫
        (bisimplicialDiagonalIso W).hom =
      (bisimplicialDiagonalIso V).hom ▷ Δ[1] ≫
        weakNaturalTransformationCylinder V W (hF).rebase (hM).rebase
          (normalizedWeakTransformation hF hM (perfectScalarInclusionNat X r))
          (normalizedWeakTransformation_weak hF hM (perfectScalarInclusionNat X r)
            (perfectScalarInclusionNat_openWeak j r q hq)) := by
  ext n z
  apply Subtype.ext
  rfl

/-- The whole old diagonal cylinder matches the ordinary inclusion through the actual isos. -/
theorem perfectOpenScalarInclusionDiagonalRealization
    (t : unitInterval) (x : |SSet.diagonalSSet (bisimplicialSSet V)|) :
    SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy
          (normalizedMiddleTransformationHomotopy V W
            (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
    X.toRingedSpace))))) (perfectScalarInclusionNat X r)
            (QuotientRows.oneIdToZero W) (perfectScalarConeProjectionNat X r)
            (perfectOpenScalarIdentityCofibrationSequence j)
            (perfectOpenScalarCofibrationSequence j r)
            (perfectScalarInclusionNat X r) (perfectScalarInclusionNat_openWeak j r q hq))
          (t, x)) =
      perfectOpenScalarInclusionRealizationHomotopy j r q hq
        (t, SSet.toTop.map (bisimplicialDiagonalIso V).hom x) :=
  realizationSimplicialHomotopy_square _ _ _ _
    (perfectOpenScalarInclusionDiagonalCylinder j r q hq) t x

end AlgebraicGeometry.Scheme.Modules

-- COL-0324 references
attribute [colib_ref "quillen"
  "PerfectComplexes/Spectrum/ScalarCofiberInclusionDiagonal.lean:1-74"
  "adaptation" "Actual whole tracks, canonical normalization and operation comparison"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarInclusionDiagonalCylinder
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarInclusionDiagonalRealization
