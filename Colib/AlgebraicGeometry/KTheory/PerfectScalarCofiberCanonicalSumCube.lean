/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberCanonicalPairCylinder
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberFineProjectionCubePath
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberSumNormalizationSquare
public import Colib.KTheory.Waldhausen.Additivity.CompactCoproductChangeWeak

/-! # The actual canonical sum cylinder on the original subdivision cube

The public acyclic cone uses the original first restriction, while the normalized identity
uses the distinct right restriction. Actual product projections identify their fine target
cubes with the compact coproduct cubes. The original canonical null is retained with its
single reversal and explicit source transport. The full reversed canonical sum cylinder is
then identified at every time and spatial point by product-comparison injectivity.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberCanonicalSumCube.lean:34-379`
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
local instance canonicalSumCoproducts (X : Scheme.{u}) : HasBinaryCoproducts
  (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :=
  Additivity.hasBinaryCoproducts (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "N" => perfectOpenNested j
local notation "W" => NestedWeakEquivalences.coarse N
local notation "PV" => productStructure V V
local notation "PW" => productStructure W W
local notation "hA" => perfectOpenScalarConeFunctor_waldhausenExact j r q hq
local notation "hR" => perfectOpenScalarIdentityRebase_fineExact j
local notation "hD" => IsExact.comp (IsExact.rebase hA) (acyclicInclusion_exact N)
local notation "hF" => changeWeak_exact N
local notation "S" => OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V

/-- Fine exactness of the literal zero/right pair, before taking its coproduct. -/
theorem perfectOpenScalarZeroPairFine_exact :
    IsExact (PV).cof (PV).weq (PV).cof (PV).weq
      ((zeroFunctor (C := ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
        X.toRingedSpace))) W).prod
        (CategoryTheory.rebaseFunctor (𝟭 (ObjectProperty.FullSubcategory
          (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))) (V).zero (W).zero
          (((hF).zero (V).isZero).iso (W).isZero))) :=
  pair_exact PV V V ((fst_exact V V).comp (zeroFunctor_isExact V V))
    ((snd_exact V V).comp hR)

/-- Fine exactness of the literal public cone/right pair, before taking its coproduct. -/
theorem perfectOpenScalarConePairFine_exact :
    IsExact (PV).cof (PV).weq (PV).cof (PV).weq
      (((CategoryTheory.rebaseFunctor (perfectOpenScalarConeFunctor j r q hq)
        (V).zero (acyclicStructure N).zero
        (((hA).zero (V).isZero).iso (acyclicStructure N).isZero)) ⋙
          acyclicInclusion N).prod
        (CategoryTheory.rebaseFunctor (𝟭 (ObjectProperty.FullSubcategory
          (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))) (V).zero (W).zero
          (((hF).zero (V).isZero).iso (W).isZero))) :=
  pair_exact PV V V ((fst_exact V V).comp hD) ((snd_exact V V).comp hR)

/-- Both fine zero-pair projections are the original functorial maps. -/
theorem perfectOpenScalarZeroPairFine_projection (x : (PV).Delooping) :
    Product.deloopingComparison V V
        (deloopingMap (perfectOpenScalarZeroPairFine_exact j) x) =
      ((V).kBasepoint, deloopingMap hR (deloopingMap (snd_exact V V) x)) := by
  have hf : deloopingMap (perfectOpenScalarZeroPairFine_exact j) ≫
      deloopingMap (fst_exact V V) =
        deloopingMap (fst_exact V V) ≫ deloopingMap (zeroFunctor_isExact V V) := by
    rw [deloopingMap_comp_deloopingMap, deloopingMap_comp_deloopingMap]
  have hs : deloopingMap (perfectOpenScalarZeroPairFine_exact j) ≫
      deloopingMap (snd_exact V V) =
        deloopingMap (snd_exact V V) ≫ deloopingMap hR := by
    rw [deloopingMap_comp_deloopingMap, deloopingMap_comp_deloopingMap]
  apply _root_.Prod.ext
  · exact (ConcreteCategory.congr_hom hf x).trans
      (DFunLike.congr_fun (deloopingMap_zeroFunctor V V) _)
  · exact ConcreteCategory.congr_hom hs x

/-- Both fine cone-pair projections are the original functorial maps. -/
theorem perfectOpenScalarConePairFine_projection (x : (PV).Delooping) :
    Product.deloopingComparison V V
        (deloopingMap (perfectOpenScalarConePairFine_exact j r q hq) x) =
      (deloopingMap hD (deloopingMap (fst_exact V V) x),
        deloopingMap hR (deloopingMap (snd_exact V V) x)) := by
  have hf : deloopingMap (perfectOpenScalarConePairFine_exact j r q hq) ≫
      deloopingMap (fst_exact V V) =
        deloopingMap (fst_exact V V) ≫ deloopingMap hD := by
    rw [deloopingMap_comp_deloopingMap, deloopingMap_comp_deloopingMap]
  have hs : deloopingMap (perfectOpenScalarConePairFine_exact j r q hq) ≫
      deloopingMap (snd_exact V V) =
        deloopingMap (snd_exact V V) ≫ deloopingMap hR := by
    rw [deloopingMap_comp_deloopingMap, deloopingMap_comp_deloopingMap]
  exact _root_.Prod.ext (ConcreteCategory.congr_hom hf x) (ConcreteCategory.congr_hom hs x)

variable (n : ℕ) (p : GenLoop (Fin (n + 1))
  |SSet.diagonalSSet
    (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (RingedSpace.perfectComplexesWaldhausen
      X.toRingedSpace))|
  (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)))

/-- The public acyclic cone cube on the original first restriction. -/
def perfectOpenScalarCanonicalAcyclicCube :
    GenLoop (Fin (n + 1)) (acyclicStructure N).Delooping (acyclicStructure N).kBasepoint :=
  GenLoop.postcomp (deloopingMap (hA).rebase).hom (KMap_basepoint hA)
    (perfectScalarProjectionInputCube n p)

/-- Its actual fine inclusion, before the original change of weak equivalences. -/
def perfectOpenScalarCanonicalConeCube :
    GenLoop (Fin (n + 1)) (V).Delooping (V).kBasepoint :=
  GenLoop.postcomp (acyclicInclusionMap N) (acyclicInclusionMap_basepoint N)
    (perfectOpenScalarCanonicalAcyclicCube j r q hq n p)

/-- The second cube uses the distinct original right restriction and same identity rebase. -/
def perfectOpenScalarCanonicalRightCube :
    GenLoop (Fin (n + 1)) (V).Delooping (V).kBasepoint :=
  GenLoop.postcomp (deloopingMap hR).hom
    (deloopingMap_basepoint_of_zeroEq hR (perfectOpenScalarProjectionIdentity_zero j))
    (GenLoop.postcomp (separatedRightDeloopingMap V)
      (separatedRightDeloopingMap_basepoint V) p)

/-- The literal coarse acyclic inclusion of the same public acyclic cube. -/
def perfectOpenScalarCanonicalCoarseConeCube :
    GenLoop (Fin (n + 1)) (W).Delooping (W).kBasepoint :=
  GenLoop.postcomp (deloopingMap (acyclicInclusion_coarse_exact N)).hom
    (deloopingMap_basepoint_of_zeroEq (acyclicInclusion_coarse_exact N)
      (by simpa only [acyclicInclusion_zero] using (N).coarse_zero.symm))
    (perfectOpenScalarCanonicalAcyclicCube j r q hq n p)

/-- The source transport is actual inclusion/change-weak composition at every spatial point. -/
theorem perfectOpenScalarCanonicalConeCube_changeWeak :
    perfectOpenScalarCubeChangeWeak j n (perfectOpenScalarCanonicalConeCube j r q hq n p) =
      perfectOpenScalarCanonicalCoarseConeCube j r q hq n p := by
  apply GenLoop.ext
  intro z
  exact ConcreteCategory.congr_hom
    (deloopingMap_comp_deloopingMap (acyclicInclusion_exact N) (changeWeak_exact N))
    (perfectOpenScalarCanonicalAcyclicCube j r q hq n p z)

/-- The original null path, with its literal coarse-inclusion source. -/
def perfectOpenScalarCanonicalNullRaw :
    Path (perfectOpenScalarCanonicalCoarseConeCube j r q hq n p) GenLoop.const :=
  (genLoopPathOfHomotopyRel (GenLoop.postcompHomotopy
    (show (changeWeakMap N).comp (acyclicInclusionMap N) (acyclicStructure N).kBasepoint =
      (W).kBasepoint from
        (congrArg (changeWeakMap N) (acyclicInclusionMap_basepoint N)).trans
          (changeWeakMap_basepoint N)) rfl
    (acyclicNullhomotopy N) (acyclicNullhomotopy_fixed_zero N)
    (perfectOpenScalarCanonicalAcyclicCube j r q hq n p))).cast
      (perfectOpenScalarCanonicalConeCube_changeWeak j r q hq n p).symm rfl

/-- The exact source cast has the new fine-image source equal to the old coarse source. -/
def perfectOpenScalarCanonicalNullPath :
    Path (perfectOpenScalarCubeChangeWeak j n
      (perfectOpenScalarCanonicalConeCube j r q hq n p)) GenLoop.const :=
  (perfectOpenScalarCanonicalNullRaw j r q hq n p).cast
    (perfectOpenScalarCanonicalConeCube_changeWeak j r q hq n p) rfl

/-- All null times retain the existing canonical reversal on the unchanged public cone. -/
theorem perfectOpenScalarCanonicalNullPath_apply (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCanonicalNullPath j r q hq n p t z =
      acyclicNullhomotopy N (t, perfectOpenScalarCanonicalAcyclicCube j r q hq n p z) := rfl

/-- The fine zero target is the actual exact target functor on the original separated pair. -/
def perfectOpenScalarZeroPairTargetCube :
    GenLoop (Fin (n + 1)) (V).Delooping (V).kBasepoint :=
  GenLoop.postcomp (deloopingMap (perfectOpenScalarZeroPairTarget_exact j)).hom
    (deloopingMap_basepoint_of_zeroEq (perfectOpenScalarZeroPairTarget_exact j)
      (perfectOpenScalarZeroPairTarget_zero j))
    (GenLoop.postcomp (separatedPairDeloopingMap V)
      (separatedPairDeloopingMap_basepoint V) p)

/-- The fine cone target is the same construction on the public acyclic cone/right pair. -/
def perfectOpenScalarConePairTargetCube :
    GenLoop (Fin (n + 1)) (V).Delooping (V).kBasepoint :=
  GenLoop.postcomp (deloopingMap (perfectOpenScalarConePairTarget_exact j r q hq)).hom
    (deloopingMap_basepoint_of_zeroEq (perfectOpenScalarConePairTarget_exact j r q hq)
      (perfectOpenScalarConePairTarget_zero j r q hq))
    (GenLoop.postcomp (separatedPairDeloopingMap V)
      (separatedPairDeloopingMap_basepoint V) p)

/-- Actual product injectivity identifies the entire fine zero target with the compact cube. -/
theorem perfectOpenScalarZeroPairTargetCube_compact :
    perfectOpenScalarZeroPairTargetCube j n p =
      coproductCube V n GenLoop.const (perfectOpenScalarCanonicalRightCube j n p) := by
  apply GenLoop.ext
  intro z
  have hs := congrArg Prod.snd (separatedPairDeloopingMap_projection V (p z))
  have hp : deloopingMap (perfectOpenScalarZeroPairFine_exact j)
      (separatedPairDeloopingMap V (p z)) =
        productCubeLift V n GenLoop.const (perfectOpenScalarCanonicalRightCube j n p) z := by
    apply Product.deloopingComparison_injective V V
    rw [perfectOpenScalarZeroPairFine_projection, productCubeLift_projection]
    exact _root_.Prod.ext rfl (congrArg (deloopingMap hR) hs)
  exact (ConcreteCategory.congr_hom
    (deloopingMap_comp_deloopingMap (perfectOpenScalarZeroPairFine_exact j)
      (coproductRebasedFunctor_exact V)).symm (separatedPairDeloopingMap V (p z))).trans
    (congrArg (coproductBasedMap V) hp)

/-- The entire fine cone target retains quotient-first cone/right order in the compact cube. -/
theorem perfectOpenScalarConePairTargetCube_compact :
    perfectOpenScalarConePairTargetCube j r q hq n p =
      coproductCube V n (perfectOpenScalarCanonicalConeCube j r q hq n p)
        (perfectOpenScalarCanonicalRightCube j n p) := by
  apply GenLoop.ext
  intro z
  have hf := congrArg Prod.fst (separatedPairDeloopingMap_projection V (p z))
  have hs := congrArg Prod.snd (separatedPairDeloopingMap_projection V (p z))
  have hp : deloopingMap (perfectOpenScalarConePairFine_exact j r q hq)
      (separatedPairDeloopingMap V (p z)) =
        productCubeLift V n (perfectOpenScalarCanonicalConeCube j r q hq n p)
          (perfectOpenScalarCanonicalRightCube j n p) z := by
    apply Product.deloopingComparison_injective V V
    rw [perfectOpenScalarConePairFine_projection, productCubeLift_projection]
    apply _root_.Prod.ext
    · exact (congrArg (deloopingMap hD) hf).trans
        (ConcreteCategory.congr_hom (deloopingMap_comp_deloopingMap (hA).rebase
          (acyclicInclusion_exact N)).symm (separatedFirstDeloopingMap V (p z)))
    · exact congrArg (deloopingMap hR) hs
  exact (ConcreteCategory.congr_hom
    (deloopingMap_comp_deloopingMap (perfectOpenScalarConePairFine_exact j r q hq)
      (coproductRebasedFunctor_exact V)).symm (separatedPairDeloopingMap V (p z))).trans
    (congrArg (coproductBasedMap V) hp)

/-- The fine zero target is exactly the old diagonal target on every original spatial point. -/
theorem perfectOpenScalarZeroPairTargetCube_diagonal (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarZeroPairTargetCube j n p z =
      SSet.toTop.map (bisimplicialDiagonalIso V).hom
        (realizedDiagonalMap (separatedPairMap V ≫
          bisimplicialSSetMap (PV).cof (PV).weq
            (perfectOpenScalarZeroPairTarget_exact j)) (p z)) := by
  have hn := DFunLike.congr_fun (realizedDiagonalMap_exact_naturality PV V
    (perfectOpenScalarZeroPairTarget_exact j)) (realizedDiagonalMap (separatedPairMap V) (p z))
  rw [realizedDiagonalMap_comp]
  exact hn.symm

/-- The fine cone target is exactly the old diagonal target on every original spatial point. -/
theorem perfectOpenScalarConePairTargetCube_diagonal (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarConePairTargetCube j r q hq n p z =
      SSet.toTop.map (bisimplicialDiagonalIso V).hom
        (realizedDiagonalMap (separatedPairMap V ≫
          bisimplicialSSetMap (PV).cof (PV).weq
            (perfectOpenScalarConePairTarget_exact j r q hq)) (p z)) := by
  have hn := DFunLike.congr_fun (realizedDiagonalMap_exact_naturality PV V
    (perfectOpenScalarConePairTarget_exact j r q hq))
      (realizedDiagonalMap (separatedPairMap V) (p z))
  rw [realizedDiagonalMap_comp]
  exact hn.symm

/-- The entire reversed pair cylinder has exactly the null and fixed-right projections. -/
theorem perfectOpenScalarCanonicalPairRealization_reversed_projection (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    Product.deloopingComparison W W
      (perfectOpenScalarCanonicalPairRealization j r q hq
        (unitInterval.symm t, separatedPairDeloopingMap V (p z))) =
      (perfectOpenScalarCanonicalNullPath j r q hq n p t z,
        perfectOpenScalarCubeChangeWeak j n (perfectOpenScalarCanonicalRightCube j n p) z) := by
  rw [perfectOpenScalarCanonicalPairRealization_projection]
  have hf : deloopingMap (fst_exact V V) (separatedPairDeloopingMap V (p z)) =
      separatedFirstDeloopingMap V (p z) :=
    congrArg Prod.fst (separatedPairDeloopingMap_projection V (p z))
  have hs : deloopingMap (snd_exact V V) (separatedPairDeloopingMap V (p z)) =
      separatedRightDeloopingMap V (p z) :=
    congrArg Prod.snd (separatedPairDeloopingMap_projection V (p z))
  apply _root_.Prod.ext
  · exact (congrArg (fun x : (V).Delooping ↦
      realizationSimplicialHomotopy (perfectOpenScalarCanonicalLeftHomotopy j r q hq)
        (unitInterval.symm t, x)) hf).trans
      (perfectOpenScalarCanonicalNull_rebased_apply j r q hq t
        (separatedFirstDeloopingMap V (p z))).symm
  · exact (congrArg (deloopingMap (hF).rebase) hs).trans
      (ConcreteCategory.congr_hom
        (deloopingMap_comp_deloopingMap hR (changeWeak_exact N)).symm
        (separatedRightDeloopingMap V (p z)))

/-- Actual product injectivity recovers the whole compact pair, with no inverse choice. -/
theorem perfectOpenScalarCanonicalPairRealization_reversed_compact (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCanonicalPairRealization j r q hq
        (unitInterval.symm t, separatedPairDeloopingMap V (p z)) =
      productCubeLift W n (perfectOpenScalarCanonicalNullPath j r q hq n p t)
        (perfectOpenScalarCubeChangeWeak j n (perfectOpenScalarCanonicalRightCube j n p)) z :=
  Product.deloopingComparison_injective W W
    ((perfectOpenScalarCanonicalPairRealization_reversed_projection j r q hq n p t z).trans
      (productCubeLift_projection W n _ _ z).symm)

/-- The ordinary sum cylinder is the literal coproduct whiskering of the original pair. -/
def perfectOpenScalarCanonicalSumHomotopy :
    SSet.Homotopy
      (sSetMap ((perfectOpenScalarCanonicalPairZero_exact j).comp
        (coproductRebasedFunctor_exact W)))
      (sSetMap ((perfectOpenScalarCanonicalPairCone_exact j r q hq).comp
        (coproductRebasedFunctor_exact W))) :=
  weakNaturalTransformationHomotopy PV W
    ((perfectOpenScalarCanonicalPairZero_exact j).comp (coproductRebasedFunctor_exact W))
    ((perfectOpenScalarCanonicalPairCone_exact j r q hq).comp
      (coproductRebasedFunctor_exact W))
    (perfectOpenScalarCanonicalSumTransformation j r q hq)
    (fun KL ↦ perfectOpenScalarCanonicalSumTransformation_weak j r q hq KL.1 KL.2)

/-- The whole sum cylinder is the actual coproduct image of the whole pair cylinder. -/
theorem perfectOpenScalarCanonicalSumCylinder_postcompose :
    (perfectOpenScalarCanonicalPairHomotopy j r q hq).h ≫
        sSetMap (coproductRebasedFunctor_exact W) =
      (perfectOpenScalarCanonicalSumHomotopy j r q hq).h := by
  ext k z
  apply Subtype.ext
  exact nerveCylinderDiagram_postcomp
    (whiskerLeft z.1.val (perfectOpenScalarCanonicalPairTransformation j r q hq))
    (coproductRebasedFunctor W) z.2.down

/-- The old canonical diagonal cylinder is the same ordinary cylinder on the actual pair map. -/
theorem perfectOpenScalarCanonicalSumDiagonalCylinder :
    (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq).h ≫
        (bisimplicialDiagonalIso W).hom =
      (SSet.diagonalMap (separatedPairMap V) ≫ (bisimplicialDiagonalIso PV).hom) ▷ Δ[1] ≫
        (perfectOpenScalarCanonicalSumHomotopy j r q hq).h := by
  ext k z
  apply Subtype.ext
  rfl

/-- Every original sum time is the coproduct of the actual product-valued cylinder. -/
theorem perfectOpenScalarCanonicalSumDiagonalRealization (t : unitInterval)
    (x : |SSet.diagonalSSet S|) :
    SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq)
          (t, x)) =
      coproductBasedMap W (perfectOpenScalarCanonicalPairRealization j r q hq
        (t, separatedPairDeloopingMap V x)) := by
  have hd := realizationSimplicialHomotopy_square
    (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq)
    (perfectOpenScalarCanonicalSumHomotopy j r q hq)
    (SSet.diagonalMap (separatedPairMap V) ≫ (bisimplicialDiagonalIso PV).hom)
    (bisimplicialDiagonalIso W).hom
    (perfectOpenScalarCanonicalSumDiagonalCylinder j r q hq) t x
  have hp := realizationSimplicialHomotopy_naturality
    (perfectOpenScalarCanonicalPairHomotopy j r q hq)
    (perfectOpenScalarCanonicalSumHomotopy j r q hq) (𝟙 _)
    (sSetMap (coproductRebasedFunctor_exact W))
    (by simpa only [id_whiskerRight, Category.id_comp] using
      perfectOpenScalarCanonicalSumCylinder_postcompose j r q hq)
    t (separatedPairDeloopingMap V x)
  rw [SSet.toTop.map_id] at hp
  simp only [TopCat.id_app] at hp
  rw [SSet.toTop.map_comp] at hd
  exact hd.trans hp.symm

/-- The complete reversed old sum edge is exactly the compact canonical null/right path. -/
theorem perfectOpenScalarCanonicalSumDiagonalRealization_reversed_compact
    (t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq)
          (unitInterval.symm t, p z)) =
      coproductCubePath W n (perfectOpenScalarCanonicalNullPath j r q hq n p)
        (Path.refl (perfectOpenScalarCubeChangeWeak j n
          (perfectOpenScalarCanonicalRightCube j n p))) t z := by
  rw [perfectOpenScalarCanonicalSumDiagonalRealization,
    perfectOpenScalarCanonicalPairRealization_reversed_compact]
  rfl

/-- The full compact null/right comparison keeps every spatial boundary at every time. -/
theorem perfectOpenScalarCanonicalSumDiagonalRealization_reversed_boundary
    (t : unitInterval) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq)
          (unitInterval.symm t, p z)) = (W).kBasepoint := by
  rw [perfectOpenScalarCanonicalSumDiagonalRealization_reversed_compact]
  exact (coproductCubePath W n (perfectOpenScalarCanonicalNullPath j r q hq n p)
    (Path.refl (perfectOpenScalarCubeChangeWeak j n
      (perfectOpenScalarCanonicalRightCube j n p))) t).property z hz

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0317",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberCanonicalSumCube.lean:34-379"
    "adaptation"
    "Actual scalar normalization and canonical fiber maps on the unchanged subdivision cube"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCanonicalSumDiagonalRealization
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCanonicalSumDiagonalRealization_reversed_compact
AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCanonicalSumDiagonalRealization_reversed_boundary
