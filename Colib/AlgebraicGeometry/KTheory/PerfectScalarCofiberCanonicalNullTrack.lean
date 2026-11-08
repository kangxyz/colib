/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberCanonicalNull
public import Colib.KTheory.Waldhausen.Iterated.NormalizationPasting
public import Colib.Topology.Prespectrum.RelativeHomotopyPasting

/-!
# The entire original scalar canonical-null pasting

The actual maps, whole tracks, signs and independent parameters are retained.
-/
/-! Implementation provenance:
    `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberCanonicalNull.lean`
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
open Topology.LoopPrespectrum
open scoped Topology Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "N" => perfectOpenNested j
local notation "W" => NestedWeakEquivalences.coarse N
local notation "A" => perfectOpenScalarConeFunctor j r q hq
local notation "hA" => perfectOpenScalarConeFunctor_waldhausenExact j r q hq
local notation "hC" =>
  Additivity.IsCofibrationSequence.exactH (perfectOpenScalarCofibrationSequence j r)
local notation "hZ" =>
  Additivity.IsCofibrationSequence.exactH (perfectOpenScalarIdentityCofibrationSequence j)
local notation "Z" => zeroFunctor (C := ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) W
local notation "Ar" => CategoryTheory.rebaseFunctor A (Structure.zero V)
  (Structure.zero (acyclicStructure N))
  (Limits.IsZero.iso (IsExact.zero hA (Structure.isZero V))
    (Structure.isZero (acyclicStructure N)))
local notation "hD" => IsExact.comp (IsExact.rebase hA) (acyclicInclusion_coarse_exact N)

/-- The normalized zero-to-cone cylinder, with no additional normalization. -/
def perfectOpenScalarNormalizedZeroToConeHomotopy :
    Homotopy (originalPrespectrumMap V W (hZ).rebase (CategoryTheory.rebaseFunctor_obj_base _ _ _
    _))
      (originalPrespectrumMap V W (hC).rebase (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)) :=
  originalPrespectrumTransformationHomotopy V W (hZ).rebase (hC).rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    (normalizedWeakTransformation hZ hC (perfectOpenScalarZeroToCone j r q hq))
    (normalizedWeakTransformation_weak hZ hC (perfectOpenScalarZeroToCone j r q hq)
      (perfectOpenScalarZeroToCone_weak j r q hq))

/-- The old cylinder of the actual cone normalization isomorphism. -/
def perfectOpenScalarConeNormalizationHomotopy :
    Homotopy (originalPrespectrumMap V W (hC).rebase (CategoryTheory.rebaseFunctor_obj_base _ _ _
    _))
      (originalPrespectrumMap V W hD (perfectOpenScalarAcyclicConeRebase_zero j r q hq)) :=
  originalPrespectrumTransformationHomotopy V W (hC).rebase hD
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) (perfectOpenScalarAcyclicConeRebase_zero j r q
    hq)
    (perfectOpenScalarConeNormalizationIso j r q hq).hom (fun _ => (W).weq_iso _ inferInstance)

/-- The old inverse zero-normalization cylinder, retaining its literal endpoints. -/
def perfectOpenScalarZeroNormalizationHomotopy :
    Homotopy (originalPrespectrumMap V W (hZ).rebase (CategoryTheory.rebaseFunctor_obj_base _ _ _
    _))
      (originalPrespectrumMap V W (zeroFunctor_isExact V W) rfl) :=
  originalPrespectrumTransformationHomotopy V W (hZ).rebase (zeroFunctor_isExact V W)
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) rfl
    (perfectOpenScalarZeroRebaseIso j).inv (fun _ => (W).weq_iso _ inferInstance)

/-- The original zero-to-inclusion track on the public acyclic cone rebase. -/
def perfectOpenScalarRebasedZeroToConeHomotopy :
    Homotopy (originalPrespectrumMap V W (zeroFunctor_isExact V W) rfl)
      (originalPrespectrumMap V W hD (perfectOpenScalarAcyclicConeRebase_zero j r q hq)) :=
  originalPrespectrumTransformationHomotopy V W (zeroFunctor_isExact V W) hD
    rfl (perfectOpenScalarAcyclicConeRebase_zero j r q hq)
    (perfectOpenScalarRebasedZeroToCone j r q hq)
    (fun K => zeroToAcyclicInclusion_weak N ((Ar).obj K))

/-- The same zero/cone square supplies a genuine relative comparison at every level. -/
def perfectOpenScalarZeroNormalizationTrack :
    ((perfectOpenScalarNormalizedZeroToConeHomotopy j r q hq).trans
      (perfectOpenScalarConeNormalizationHomotopy j r q hq)).RelHomotopy
      ((perfectOpenScalarZeroNormalizationHomotopy j).trans
        (perfectOpenScalarRebasedZeroToConeHomotopy j r q hq)) :=
  originalPrespectrumPastingHomotopy V W (hZ).rebase (hC).rebase (zeroFunctor_isExact V W) hD
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) (CategoryTheory.rebaseFunctor_obj_base _ _ _
    _) rfl
    (perfectOpenScalarAcyclicConeRebase_zero j r q hq)
    (normalizedWeakTransformation hZ hC (perfectOpenScalarZeroToCone j r q hq))
    (perfectOpenScalarConeNormalizationIso j r q hq).hom
    (perfectOpenScalarZeroRebaseIso j).inv (perfectOpenScalarRebasedZeroToCone j r q hq)
    (normalizedWeakTransformation_weak hZ hC (perfectOpenScalarZeroToCone j r q hq)
      (perfectOpenScalarZeroToCone_weak j r q hq))
    (fun _ => (W).weq_iso _ inferInstance) (fun _ => (W).weq_iso _ inferInstance)
    (fun K => zeroToAcyclicInclusion_weak N ((Ar).obj K))
    (perfectOpenScalarZeroNormalizationSquare j r q hq)

/-- Rotation retains both normalization edges and reverses the canonical zero edge once. -/
def perfectOpenScalarCanonicalNullTriangle :
    ((perfectOpenScalarConeNormalizationHomotopy j r q hq).trans
      (perfectOpenScalarRebasedZeroToConeHomotopy j r q hq).symm).RelHomotopy
      ((perfectOpenScalarNormalizedZeroToConeHomotopy j r q hq).symm.trans
        (perfectOpenScalarZeroNormalizationHomotopy j)) :=
  (perfectOpenScalarZeroNormalizationTrack j r q hq).rotate.symm

end AlgebraicGeometry.Scheme.Modules

-- COL-0324 references
attribute [colib_ref "quillen"
  "PerfectComplexes/ScalarCofiberCanonicalNull.lean:1-219"
  "adaptation" "Actual whole tracks, canonical normalization and operation comparison"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarNormalizedZeroToConeHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarConeNormalizationHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarZeroNormalizationHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarRebasedZeroToConeHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarZeroNormalizationTrack
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCanonicalNullTriangle

attribute [colib_tag "COL-0324"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCanonicalNullTriangle
