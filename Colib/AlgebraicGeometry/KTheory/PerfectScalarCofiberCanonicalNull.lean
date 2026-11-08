/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberSequenceMap
public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakNaturalTransformationNaturality
public import Colib.Topology.Realization.HomotopyNaturality

/-!
# The scalar cone's exact normalization and canonical acyclic null

The coarse cone normalization is joined to the public acyclic cone normalization by the actual
inclusion-whiskered rebase isomorphism. The categorical zero-normalization square retains both
normalization edges. The ordinary canonical null is the original zero-to-inclusion cylinder,
reversed once, and the zero-normalization cylinder is constant at every input. Levelwise
relative squares and rotated prespectrum pasting remain future work. No fiber filler or
cancellation of the separated identity summand is asserted.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberCanonicalNull.lean:34-100, 162-219`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, universes,
normalizations, time coordinates and spatial boundaries are retained. -/
@[expose] public section
open Topology SSet

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry MonoidalCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
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
local notation "Z" =>
  zeroFunctor (C := ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
    X.toRingedSpace))) W
local notation "Ar" => CategoryTheory.rebaseFunctor A (Structure.zero V)
  (Structure.zero (acyclicStructure N))
  (Limits.IsZero.iso (IsExact.zero hA (Structure.isZero V))
    (Structure.isZero (acyclicStructure N)))
local notation "hD" => IsExact.comp (IsExact.rebase hA) (acyclicInclusion_coarse_exact N)

/-- The existing coarse normalization of the literal scalar cone. -/
def perfectOpenScalarConeRebaseIso :
    perfectScalarConeFunctor X r ≅
      CategoryTheory.rebaseFunctor (perfectScalarConeFunctor X r) (V).zero (W).zero
        (((hC).zero (V).isZero).iso (W).isZero) :=
  CategoryTheory.rebaseFunctorIso _ _ _ _

/-- The public acyclic cone K-map uses this exact inherited normalization. -/
def perfectOpenScalarAcyclicConeRebaseIso : A ≅ Ar :=
  CategoryTheory.rebaseFunctorIso _ _ _ _

/-- The original zero functor is normalized using the source sequence's exact witness. -/
def perfectOpenScalarZeroRebaseIso :
    Z ≅ CategoryTheory.rebaseFunctor Z (V).zero (W).zero (((hZ).zero (V).isZero).iso (W).isZero) :=
  CategoryTheory.rebaseFunctorIso _ _ _ _

/-- The actual cone normalization comparison, with its inclusion-whiskered second factor. -/
def perfectOpenScalarConeNormalizationIso :
    CategoryTheory.rebaseFunctor (perfectScalarConeFunctor X r) (V).zero (W).zero
        (((hC).zero (V).isZero).iso (W).isZero) ≅ Ar ⋙ acyclicInclusion N :=
  (perfectOpenScalarConeRebaseIso j r).symm ≪≫
    Functor.isoWhiskerRight (perfectOpenScalarAcyclicConeRebaseIso j r q hq)
      (acyclicInclusion N)

/-- The cone normalization edge is an actual fine weak equivalence on every coefficient. -/
theorem perfectOpenScalarConeNormalizationIso_fineWeak (K : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (V).weq ((perfectOpenScalarConeNormalizationIso j r q hq).hom.app K) :=
  (V).weq_iso _ inferInstance

/-- The public acyclic rebase followed by the original inclusion retains the chosen zero. -/
theorem perfectOpenScalarAcyclicConeRebase_zero :
    (Ar ⋙ acyclicInclusion N).obj (V).zero = (W).zero := by
  change ((Ar).obj (V).zero).obj = (W).zero
  rw [CategoryTheory.rebaseFunctor_obj_base]
  exact (N).zero_eq.symm

/-- The zero edge on the actual public acyclic rebase is the literal original whiskering. -/
def perfectOpenScalarRebasedZeroToCone : Z ⟶ Ar ⋙ acyclicInclusion N :=
  Functor.whiskerLeft Ar (zeroToAcyclicInclusion N)

/-- The normalization square is an equality of the full original natural transformations. -/
theorem perfectOpenScalarZeroNormalizationSquare :
    normalizedWeakTransformation hZ hC (perfectOpenScalarZeroToCone j r q hq) ≫
        (perfectOpenScalarConeNormalizationIso j r q hq).hom =
      (perfectOpenScalarZeroRebaseIso j).inv ≫ perfectOpenScalarRebasedZeroToCone j r q hq := by
  apply NatTrans.ext
  funext K
  exact ((W).isZero.of_iso ((perfectOpenScalarZeroRebaseIso j).app K).symm).eq_of_src _ _

/-- Normalizing a constant chosen-zero functor keeps zero at every input object. -/
theorem perfectOpenScalarZeroRebase_obj (K : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (CategoryTheory.rebaseFunctor Z (V).zero (W).zero (((hZ).zero (V).isZero).iso (W).isZero)).obj K
      =
      (W).zero := by
  classical
  simp [CategoryTheory.rebaseFunctor, CategoryTheory.rebaseObj, zeroFunctor]

/-- The whole zero-normalization cylinder is the constant map, beyond its zero face. -/
theorem perfectOpenScalarZeroNormalizationCylinder_constant :
    weakNaturalTransformationCylinder V W (hZ).rebase (zeroFunctor_isExact V W)
        (perfectOpenScalarZeroRebaseIso j).inv (fun _ => (W).weq_iso _ inferInstance) =
      SSet.const (zeroSimplex (W).cof (W).weq (W).zero (W).isZero (Opposite.op ⦋0⦌)) := by
  ext n z
  apply Subtype.ext
  exact nerveCylinderDiagram_eq_const_of_zero _ (W).zero (W).isZero
    (fun p => perfectOpenScalarZeroRebase_obj j (z.1.val.obj p)) (fun _ => rfl) z.2.down

/-- Every ordinary input and every time gives the actual chosen zero. -/
theorem perfectOpenScalarZeroNormalizationRealization_constant
    (t : unitInterval) (x : (V).Delooping) :
    weakNaturalTransformationRealizationHomotopy V W (hZ).rebase (zeroFunctor_isExact V W)
        (perfectOpenScalarZeroRebaseIso j).inv (fun _ => (W).weq_iso _ inferInstance) (t, x) =
      (W).kBasepoint := by
  change SSet.toTop.map
    (weakNaturalTransformationCylinder V W (hZ).rebase (zeroFunctor_isExact V W)
      (perfectOpenScalarZeroRebaseIso j).inv (fun _ => (W).weq_iso _ inferInstance))
    ((realizationCylinderIso _).inv (x, ULift.up t)) = _
  rw [perfectOpenScalarZeroNormalizationCylinder_constant]
  exact realization_const_apply _ _

/-- The entire original canonical null is exactly the reversed whiskered cylinder on this rebase. -/
theorem perfectOpenScalarCanonicalNull_rebased_apply
    (t : unitInterval) (x : (V).Delooping) :
    acyclicNullhomotopy N (t, deloopingMap (hA).rebase x) =
      weakNaturalTransformationRealizationHomotopy V W
        ((hA).rebase.comp (zeroFunctor_isExact (acyclicStructure N) W)) hD
        (perfectOpenScalarRebasedZeroToCone j r q hq)
        (fun K => zeroToAcyclicInclusion_weak N ((Ar).obj K)) (unitInterval.symm t, x) := by
  have h := weakNaturalTransformationCylinder_precompose V (acyclicStructure N) W
    (zeroFunctor_isExact (acyclicStructure N) W) (acyclicInclusion_coarse_exact N)
    (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N) (hA).rebase
  have h' := realizationSimplicialHomotopy_naturality
    (weakNaturalTransformationHomotopy (acyclicStructure N) W
      (zeroFunctor_isExact (acyclicStructure N) W) (acyclicInclusion_coarse_exact N)
      (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N))
    (weakNaturalTransformationHomotopy V W
      ((hA).rebase.comp (zeroFunctor_isExact (acyclicStructure N) W)) hD
      (perfectOpenScalarRebasedZeroToCone j r q hq)
      (fun K => zeroToAcyclicInclusion_weak N ((Ar).obj K)))
    (sSetMap (hA).rebase) (𝟙 _) (by
      simpa only [Category.comp_id, weakNaturalTransformationHomotopy,
        perfectOpenScalarRebasedZeroToCone] using h)
    (unitInterval.symm t) x
  rw [SSet.toTop.map_id] at h'
  simp only [TopCat.id_app] at h'
  convert h' using 1 <;> rfl

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberCanonicalNull.lean:34-100, 162-219"
    "adaptation"
    "The exact normalization square and whole once-reversed canonical null"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarZeroNormalizationSquare
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCanonicalNull_rebased_apply
