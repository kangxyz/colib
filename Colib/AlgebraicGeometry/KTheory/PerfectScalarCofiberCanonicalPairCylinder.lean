/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberSumNormalization
public import Colib.KTheory.Waldhausen.IdentityCylinder
public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakNaturalTransformationNaturality
public import Colib.Topology.Realization.HomotopySquare

/-! # The actual quotient-first canonical pair cylinder

The literal zero-to-acyclic-inclusion transformation is paired with the identity on the same
canonically rebased identity functor. Its whole first projection is the original canonical
cylinder; its whole second projection is constant in time. Both equations hold before
realization and retain the actual inverse cylinder afterward. No compact endpoint or fiber
comparison is assumed.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberCanonicalPairCylinder.lean:34-173`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, universes,
normalizations, time coordinates and spatial boundaries are retained. -/
@[expose] public section
open Topology SSet

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
  CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.Product MonoidalCategory
open scoped Topology Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "N" => perfectOpenNested j
local notation "W" => NestedWeakEquivalences.coarse N
local notation "hF" => changeWeak_exact N
local notation "Fbar" =>
  CategoryTheory.rebaseFunctor (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X
    := X.toRingedSpace)))) (Structure.zero V)
  (Structure.zero W) (Limits.IsZero.iso (IsExact.zero hF (Structure.isZero V))
    (Structure.isZero W))
local notation "A" => perfectOpenScalarConeFunctor j r q hq
local notation "hA" => perfectOpenScalarConeFunctor_waldhausenExact j r q hq
local notation "Ar" => CategoryTheory.rebaseFunctor A (Structure.zero V)
  (Structure.zero (acyclicStructure N))
  (Limits.IsZero.iso (IsExact.zero hA (Structure.isZero V))
    (Structure.isZero (acyclicStructure N)))
local notation "D" => Ar ⋙ acyclicInclusion N
local notation "hD" => IsExact.comp (IsExact.rebase hA) (acyclicInclusion_coarse_exact N)
local notation "Z" =>
  zeroFunctor (C := ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
    X.toRingedSpace))) W
local notation "PV" => productStructure V V
local notation "PW" => productStructure W W

/-- The actual zero/identity pair is exact for the inherited coarse target structure. -/
theorem perfectOpenScalarCanonicalPairZero_exact :
    IsExact (PV).cof (PV).weq (PW).cof (PW).weq ((Z).prod Fbar) :=
  pair_exact PV W W ((fst_exact V V).comp (zeroFunctor_isExact V W))
    ((snd_exact V V).comp (hF).rebase)

/-- The actual public acyclic cone/identity pair is exact for that same product structure. -/
theorem perfectOpenScalarCanonicalPairCone_exact :
    IsExact (PV).cof (PV).weq (PW).cof (PW).weq ((D).prod Fbar) :=
  pair_exact PV W W ((fst_exact V V).comp hD) ((snd_exact V V).comp (hF).rebase)

/-- The original weak cylinder on the literal quotient-first pair transformation. -/
def perfectOpenScalarCanonicalPairHomotopy :
    SSet.Homotopy (sSetMap (perfectOpenScalarCanonicalPairZero_exact j))
      (sSetMap (perfectOpenScalarCanonicalPairCone_exact j r q hq)) :=
  weakNaturalTransformationHomotopy PV PW (perfectOpenScalarCanonicalPairZero_exact j)
    (perfectOpenScalarCanonicalPairCone_exact j r q hq)
    (perfectOpenScalarCanonicalPairTransformation j r q hq)
    (fun KL ↦ perfectOpenScalarCanonicalPairTransformation_weak j r q hq KL.1 KL.2)

/-- The first factor is precisely the unchanged original zero-to-inclusion cylinder. -/
def perfectOpenScalarCanonicalLeftHomotopy :
    SSet.Homotopy (sSetMap (zeroFunctor_isExact V W)) (sSetMap hD) :=
  weakNaturalTransformationHomotopy V W (zeroFunctor_isExact V W) hD
    (perfectOpenScalarRebasedZeroToCone j r q hq)
    (fun K ↦ zeroToAcyclicInclusion_weak N ((Ar).obj K))

/-- The full first projected cylinder retains every original cut and input morphism. -/
theorem perfectOpenScalarCanonicalPairHomotopy_fst :
    (perfectOpenScalarCanonicalPairHomotopy j r q hq).h ≫ sSetMap (fst_exact W W) =
      sSetMap (fst_exact V V) ▷ Δ[1] ≫
        (perfectOpenScalarCanonicalLeftHomotopy j r q hq).h := by
  ext n z
  apply Subtype.ext
  exact nerveCylinderDiagram_postcomp
    (whiskerLeft z.1.val (perfectOpenScalarCanonicalPairTransformation j r q hq))
    (CategoryTheory.Prod.fst (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
      X.toRingedSpace))) (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
      X.toRingedSpace)))) z.2.down

/-- The entire second cylinder is the first projection followed by the same original map. -/
theorem perfectOpenScalarCanonicalPairHomotopy_snd :
    (perfectOpenScalarCanonicalPairHomotopy j r q hq).h ≫ sSetMap (snd_exact W W) =
      CartesianMonoidalCategory.fst (sSet (PV).cof (PV).weq) Δ[1] ≫
        sSetMap ((snd_exact V V).comp (hF).rebase) := by
  ext n z
  apply Subtype.ext
  refine (nerveCylinderDiagram_postcomp
    (whiskerLeft z.1.val (perfectOpenScalarCanonicalPairTransformation j r q hq))
    (CategoryTheory.Prod.snd (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
      X.toRingedSpace))) (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
      X.toRingedSpace)))) z.2.down).trans ?_
  exact nerveCylinderDiagram_identity
    (z.1.val ⋙ CategoryTheory.Prod.snd (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
      (X := X.toRingedSpace))) (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
      X.toRingedSpace))) ⋙ Fbar) z.2.down

/-- The actual product-valued realization retains the original finite-cylinder inverse. -/
def perfectOpenScalarCanonicalPairRealization :
    (deloopingMap (perfectOpenScalarCanonicalPairZero_exact j)).hom.Homotopy
      (deloopingMap (perfectOpenScalarCanonicalPairCone_exact j r q hq)).hom :=
  realizationSimplicialHomotopy (perfectOpenScalarCanonicalPairHomotopy j r q hq)

/-- Every first-projection time is the actual original zero-to-inclusion realization. -/
theorem perfectOpenScalarCanonicalPairRealization_fst (t : unitInterval)
    (x : (PV).Delooping) :
    deloopingMap (fst_exact W W) (perfectOpenScalarCanonicalPairRealization j r q hq (t, x)) =
      realizationSimplicialHomotopy (perfectOpenScalarCanonicalLeftHomotopy j r q hq)
        (t, deloopingMap (fst_exact V V) x) :=
  realizationSimplicialHomotopy_square _ _ _ _
    (perfectOpenScalarCanonicalPairHomotopy_fst j r q hq) t x

/-- Every second-projection time is the same actual rebased right-input map. -/
theorem perfectOpenScalarCanonicalPairRealization_snd (t : unitInterval)
    (x : (PV).Delooping) :
    deloopingMap (snd_exact W W) (perfectOpenScalarCanonicalPairRealization j r q hq (t, x)) =
      deloopingMap ((snd_exact V V).comp (hF).rebase) x := by
  have hp : (realizationCylinderIso (sSet (PV).cof (PV).weq)).inv ≫
      SSet.toTop.map (CartesianMonoidalCategory.fst (sSet (PV).cof (PV).weq) Δ[1]) =
        CartesianMonoidalCategory.fst _ _ := by
    rw [← realizationCylinderComparison_fst]
    change (realizationCylinderIso (sSet (PV).cof (PV).weq)).inv ≫
      (realizationCylinderIso (sSet (PV).cof (PV).weq)).hom ≫ _ = _
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change (SSet.toTop.map (perfectOpenScalarCanonicalPairHomotopy j r q hq).h ≫
    SSet.toTop.map (sSetMap (snd_exact W W)))
      ((realizationCylinderIso (sSet (PV).cof (PV).weq)).inv (x, ULift.up t)) = _
  rw [← SSet.toTop.map_comp, perfectOpenScalarCanonicalPairHomotopy_snd,
    SSet.toTop.map_comp]
  change ((realizationCylinderIso (sSet (PV).cof (PV).weq)).inv ≫
    SSet.toTop.map (CartesianMonoidalCategory.fst (sSet (PV).cof (PV).weq) Δ[1]) ≫
      deloopingMap ((snd_exact V V).comp (hF).rebase)) (x, ULift.up t) = _
  rw [← Category.assoc, hp]
  rfl

/-- The actual product comparison retains the complete left track and fixed right cube. -/
theorem perfectOpenScalarCanonicalPairRealization_projection (t : unitInterval)
    (x : (PV).Delooping) :
    Product.deloopingComparison W W
        (perfectOpenScalarCanonicalPairRealization j r q hq (t, x)) =
      (realizationSimplicialHomotopy (perfectOpenScalarCanonicalLeftHomotopy j r q hq)
        (t, deloopingMap (fst_exact V V) x),
        deloopingMap (hF).rebase (deloopingMap (snd_exact V V) x)) := by
  apply _root_.Prod.ext
  · exact perfectOpenScalarCanonicalPairRealization_fst j r q hq t x
  · exact (perfectOpenScalarCanonicalPairRealization_snd j r q hq t x).trans
      (ConcreteCategory.congr_hom
        (deloopingMap_comp_deloopingMap (snd_exact V V) (hF).rebase).symm x)

/-- Every pair-cylinder time fixes the actual product chosen-zero point. -/
theorem perfectOpenScalarCanonicalPairRealization_zero (t : unitInterval) :
    perfectOpenScalarCanonicalPairRealization j r q hq (t, (PV).kBasepoint) =
      (PW).kBasepoint := by
  have hz : (Fbar).obj (Structure.zero V) = Structure.zero W :=
    CategoryTheory.rebaseFunctor_obj_base (𝟭 (ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))) (Structure.zero V) (Structure.zero W)
      (Limits.IsZero.iso (IsExact.zero hF (Structure.isZero V)) (Structure.isZero W))
  exact weakNaturalTransformationRealizationHomotopy_fixed_zero PV PW
    (perfectOpenScalarCanonicalPairZero_exact j)
    (perfectOpenScalarCanonicalPairCone_exact j r q hq)
    (perfectOpenScalarCanonicalPairTransformation j r q hq)
    (fun KL ↦ perfectOpenScalarCanonicalPairTransformation_weak j r q hq KL.1 KL.2)
    (_root_.Prod.ext rfl hz)
    (_root_.Prod.ext (perfectOpenScalarAcyclicConeRebase_zero j r q hq)
      hz) t

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0317",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberCanonicalPairCylinder.lean:34-173"
    "adaptation"
    "Actual scalar normalization and canonical fiber maps on the unchanged subdivision cube"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCanonicalPairRealization_snd
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCanonicalPairRealization_projection
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCanonicalPairRealization_zero
