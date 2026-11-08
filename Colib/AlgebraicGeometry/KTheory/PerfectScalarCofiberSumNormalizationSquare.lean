/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberSumNormalization
public import Colib.KTheory.Waldhausen.Additivity.SeparatedPairMap
public import Colib.KTheory.Waldhausen.WeakGridSquareRealization
public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakNaturalTransformationNaturality

/-! # The whole quotient-first scalar normalization square

The actual separated pair grid carries the original sum edge, both full normalization
isomorphisms and the canonical sum edge. Every simplicial and continuous face is retained,
with vertical time first and horizontal time second. The same fine normalization cylinders
have their complete change-weak images, before any compact target or null-path transport.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberSumNormalizationSquare.lean:34-557`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, universes,
normalizations, time coordinates and spatial boundaries are retained. -/
@[expose] public section
open Topology SSet

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open Opposite MonoidalCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
  CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.Product
open scoped Simplicial Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules
local instance scalarNormalizationSquareCoproducts (X : Scheme.{u}) :
    HasBinaryCoproducts (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
      X.toRingedSpace))) := Additivity.hasBinaryCoproducts (RingedSpace.perfectComplexesWaldhausen
      X.toRingedSpace)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)
local notation "S" => OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V
local notation "h0w" => perfectOpenScalarIdentityCofibrationSequence j
local notation "h0f" => perfectScalarIdentityFineCofibrationSequence (X := X)
local notation "h1w" => perfectOpenScalarCofibrationSequence j r
local notation "h1f" => perfectScalarCofibrationSequence X r

/-- The old coarse zero sum map retains both original restrictions. -/
def perfectOpenScalarZeroSumMap : S ⟶ bisimplicialSSet W :=
  normalizedSumMap V W (h0w).exactH (h0w).exactF

/-- The actual zero target is applied to the original separated pair map. -/
def perfectOpenScalarZeroPairMap : S ⟶ bisimplicialSSet W :=
  separatedPairMap V ≫ bisimplicialSSetMap (productStructure V V).cof
    (productStructure V V).weq
    ((perfectOpenScalarZeroPairTarget_exact j).comp
      (changeWeak_exact (perfectOpenNested j)))

/-- The old coarse cone sum map retains both original restrictions. -/
def perfectOpenScalarConeSumMap : S ⟶ bisimplicialSSet W :=
  normalizedSumMap V W (h1w).exactH (h1w).exactF

/-- The actual cone target is applied to the original separated pair map. -/
def perfectOpenScalarConePairMap : S ⟶ bisimplicialSSet W :=
  separatedPairMap V ≫ bisimplicialSSetMap (productStructure V V).cof
    (productStructure V V).weq
    ((perfectOpenScalarConePairTarget_exact j r q hq).comp
      (changeWeak_exact (perfectOpenNested j)))

private theorem scalarSumApp_heq {F G : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
  (X := X.toRingedSpace)) × ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
  X.toRingedSpace)) ⥤ ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
  X.toRingedSpace))}
    (η : F ⟶ G) {x y : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
      X.toRingedSpace)) × ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
      X.toRingedSpace))} (h : x = y) :
    HEq (η.app x) (η.app y) := by
  subst y
  rfl

theorem scalarSumFamily_reindex {F G : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
  (X := X.toRingedSpace)) × ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
  X.toRingedSpace)) ⥤ ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
  X.toRingedSpace))}
    (η : F ⟶ G) {n n' : SimplexCategoryᵒᵖ} (ρ : n ⟶ n')
    (A : (SSet.diagonalSSet S).obj n) (x : Grid₂ n'.unop n'.unop) :
    HEq ((whiskerLeft (separatedPairGrid
        (((SSet.diagonalSSet S).map ρ A).1)) η).app x)
      ((whiskerLeft (separatedPairGrid A.1) η).app
        ((gridMap₂ ρ.unop ρ.unop).obj x)) := by
  apply scalarSumApp_heq η
  exact congrArg (fun T ↦ T.obj x) (separatedPairGrid_reindex ρ.unop ρ.unop A.1)

/-- The actual SeparatedSum transformation is whiskered by the original separated pair grid. -/
def perfectOpenScalarSeparatedSumFamily (n m : SimplexCategoryᵒᵖ)
    (A : ((S).obj n).obj m) :
    (((perfectOpenScalarZeroSumMap j).app n).app m A).1 ⟶
      (((perfectOpenScalarConeSumMap j r).app n).app m A).1 :=
  whiskerLeft (separatedPairGrid A.1) (perfectOpenScalarSeparatedSumTransformation j r q hq)

/-- The SeparatedSum family retains its own original diagonal restriction equation. -/
theorem perfectOpenScalarSeparatedSumFamily_reindex {n n' : SimplexCategoryᵒᵖ}
    (ρ : n ⟶ n') (A : (SSet.diagonalSSet S).obj n)
    (x : Grid₂ n'.unop n'.unop) :
    HEq ((perfectOpenScalarSeparatedSumFamily j r q hq n' n'
        ((SSet.diagonalSSet S).map ρ A)).app x)
      ((perfectOpenScalarSeparatedSumFamily j r q hq n n A).app
        ((gridMap₂ ρ.unop ρ.unop).obj x)) :=
  scalarSumFamily_reindex (perfectOpenScalarSeparatedSumTransformation j r q hq) ρ A x

/-- The actual CanonicalSum transformation is whiskered by the original separated pair grid. -/
def perfectOpenScalarCanonicalSumFamily (n m : SimplexCategoryᵒᵖ)
    (A : ((S).obj n).obj m) :
    (((perfectOpenScalarZeroPairMap j).app n).app m A).1 ⟶
      (((perfectOpenScalarConePairMap j r q hq).app n).app m A).1 :=
  whiskerLeft (separatedPairGrid A.1) (perfectOpenScalarCanonicalSumTransformation j r q hq)

/-- The CanonicalSum family retains its own original diagonal restriction equation. -/
theorem perfectOpenScalarCanonicalSumFamily_reindex {n n' : SimplexCategoryᵒᵖ}
    (ρ : n ⟶ n') (A : (SSet.diagonalSSet S).obj n)
    (x : Grid₂ n'.unop n'.unop) :
    HEq ((perfectOpenScalarCanonicalSumFamily j r q hq n' n'
        ((SSet.diagonalSSet S).map ρ A)).app x)
      ((perfectOpenScalarCanonicalSumFamily j r q hq n n A).app
        ((gridMap₂ ρ.unop ρ.unop).obj x)) :=
  scalarSumFamily_reindex (perfectOpenScalarCanonicalSumTransformation j r q hq) ρ A x

/-- The actual ZeroTheta transformation is whiskered by the original separated pair grid. -/
def perfectOpenScalarZeroThetaFamily (n m : SimplexCategoryᵒᵖ)
    (A : ((S).obj n).obj m) :
    (((perfectOpenScalarZeroSumMap j).app n).app m A).1 ⟶
      (((perfectOpenScalarZeroPairMap j).app n).app m A).1 :=
  whiskerLeft (separatedPairGrid A.1) (perfectOpenScalarZeroSumNormalizationIso j).hom

/-- The ZeroTheta family retains its own original diagonal restriction equation. -/
theorem perfectOpenScalarZeroThetaFamily_reindex {n n' : SimplexCategoryᵒᵖ}
    (ρ : n ⟶ n') (A : (SSet.diagonalSSet S).obj n)
    (x : Grid₂ n'.unop n'.unop) :
    HEq ((perfectOpenScalarZeroThetaFamily j n' n'
        ((SSet.diagonalSSet S).map ρ A)).app x)
      ((perfectOpenScalarZeroThetaFamily j n n A).app
        ((gridMap₂ ρ.unop ρ.unop).obj x)) :=
  scalarSumFamily_reindex (perfectOpenScalarZeroSumNormalizationIso j).hom ρ A x

/-- The actual ConeTheta transformation is whiskered by the original separated pair grid. -/
def perfectOpenScalarConeThetaFamily (n m : SimplexCategoryᵒᵖ)
    (A : ((S).obj n).obj m) :
    (((perfectOpenScalarConeSumMap j r).app n).app m A).1 ⟶
      (((perfectOpenScalarConePairMap j r q hq).app n).app m A).1 :=
  whiskerLeft (separatedPairGrid A.1) (perfectOpenScalarConeSumNormalizationIso j r q hq).hom

/-- The ConeTheta family retains its own original diagonal restriction equation. -/
theorem perfectOpenScalarConeThetaFamily_reindex {n n' : SimplexCategoryᵒᵖ}
    (ρ : n ⟶ n') (A : (SSet.diagonalSSet S).obj n)
    (x : Grid₂ n'.unop n'.unop) :
    HEq ((perfectOpenScalarConeThetaFamily j r q hq n' n'
        ((SSet.diagonalSSet S).map ρ A)).app x)
      ((perfectOpenScalarConeThetaFamily j r q hq n n A).app
        ((gridMap₂ ρ.unop ρ.unop).obj x)) :=
  scalarSumFamily_reindex (perfectOpenScalarConeSumNormalizationIso j r q hq).hom ρ A x

/-- This is exactly the original alpha family, before any realization. -/
theorem perfectOpenScalarSeparatedSumFamily_eq :
    perfectOpenScalarSeparatedSumFamily j r q hq =
      normalizedSumTransformationFamily V W (𝟙 (𝟭 (ObjectProperty.FullSubcategory
        (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
        (perfectScalarInclusionNat X r) (QuotientRows.oneIdToZero W)
        (perfectScalarConeProjectionNat X r) h0w h1w (𝟙 (𝟭 (ObjectProperty.FullSubcategory
          (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
        (perfectOpenScalarZeroToCone j r q hq) := rfl

/-- The old alpha family is weak by its original zero-to-cone and identity components. -/
theorem perfectOpenScalarSeparatedSumFamily_weak (n m : SimplexCategoryᵒᵖ)
    (A : ((S).obj n).obj m) (x : Grid₂ n.unop m.unop) :
    (W).weq ((perfectOpenScalarSeparatedSumFamily j r q hq n m A).app x) :=
  normalizedSplitEndpointTransformation_weak W (𝟙 (𝟭 (ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
    (perfectScalarInclusionNat X r) (𝟙 (𝟭 (ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))))) (QuotientRows.oneIdToZero W)
    (perfectScalarConeProjectionNat X r) (perfectOpenScalarZeroToCone j r q hq) V h0w h1w
    (perfectOpenScalarZeroToCone_weak j r q hq) (fun K ↦ (W).weq.id_mem K) _

/-- The canonical family uses the actual coarse coproduct weakness at each original pair. -/
theorem perfectOpenScalarCanonicalSumFamily_weak (n m : SimplexCategoryᵒᵖ)
    (A : ((S).obj n).obj m) (x : Grid₂ n.unop m.unop) :
    (W).weq ((perfectOpenScalarCanonicalSumFamily j r q hq n m A).app x) :=
  perfectOpenScalarCanonicalSumTransformation_weak j r q hq _ _

/-- Every zero-normalization component is the original coarse weak isomorphism. -/
theorem perfectOpenScalarZeroThetaFamily_weak (n m : SimplexCategoryᵒᵖ)
    (A : ((S).obj n).obj m) (x : Grid₂ n.unop m.unop) :
    (W).weq ((perfectOpenScalarZeroThetaFamily j n m A).app x) :=
  (W).weq_iso _ (show IsIso ((perfectOpenScalarZeroSumNormalizationIso j).hom.app
    ((separatedPairGrid A.1).obj x)) from inferInstance)

/-- Every cone-normalization component is the original coarse weak isomorphism. -/
theorem perfectOpenScalarConeThetaFamily_weak (n m : SimplexCategoryᵒᵖ)
    (A : ((S).obj n).obj m) (x : Grid₂ n.unop m.unop) :
    (W).weq ((perfectOpenScalarConeThetaFamily j r q hq n m A).app x) :=
  (W).weq_iso _ (show IsIso ((perfectOpenScalarConeSumNormalizationIso j r q hq).hom.app
    ((separatedPairGrid A.1).obj x)) from inferInstance)

/-- Whiskering the complete categorical square retains every original input component. -/
theorem perfectOpenScalarSumNormalizationFamilySquare (n m : SimplexCategoryᵒᵖ)
    (A : ((S).obj n).obj m) :
    perfectOpenScalarSeparatedSumFamily j r q hq n m A ≫
        perfectOpenScalarConeThetaFamily j r q hq n m A =
      perfectOpenScalarZeroThetaFamily j n m A ≫
        perfectOpenScalarCanonicalSumFamily j r q hq n m A := by
  unfold perfectOpenScalarSeparatedSumFamily perfectOpenScalarConeThetaFamily
    perfectOpenScalarZeroThetaFamily perfectOpenScalarCanonicalSumFamily
  rw [← Functor.whiskerLeft_comp, ← Functor.whiskerLeft_comp,
    perfectOpenScalarSumNormalizationSquare]

/-- The actual CanonicalSum weak-grid cylinder on the unchanged subdivided source. -/
def perfectOpenScalarCanonicalSumDiagonalHomotopy :
    SSet.Homotopy (SSet.diagonalMap (perfectOpenScalarZeroPairMap j))
      (SSet.diagonalMap (perfectOpenScalarConePairMap j r q hq)) :=
  diagonalWeakGridHomotopy W _ _ (perfectOpenScalarCanonicalSumFamily j r q hq)
    (perfectOpenScalarCanonicalSumFamily_weak j r q hq)
      (perfectOpenScalarCanonicalSumFamily_reindex j r q hq)

/-- The actual ZeroTheta weak-grid cylinder on the unchanged subdivided source. -/
def perfectOpenScalarZeroThetaCoarseDiagonalHomotopy :
    SSet.Homotopy (SSet.diagonalMap (perfectOpenScalarZeroSumMap j))
      (SSet.diagonalMap (perfectOpenScalarZeroPairMap j)) :=
  diagonalWeakGridHomotopy W _ _ (perfectOpenScalarZeroThetaFamily j)
    (perfectOpenScalarZeroThetaFamily_weak j) (perfectOpenScalarZeroThetaFamily_reindex j)

/-- The actual ConeTheta weak-grid cylinder on the unchanged subdivided source. -/
def perfectOpenScalarConeThetaCoarseDiagonalHomotopy :
    SSet.Homotopy (SSet.diagonalMap (perfectOpenScalarConeSumMap j r))
      (SSet.diagonalMap (perfectOpenScalarConePairMap j r q hq)) :=
  diagonalWeakGridHomotopy W _ _ (perfectOpenScalarConeThetaFamily j r q hq)
    (perfectOpenScalarConeThetaFamily_weak j r q hq) (perfectOpenScalarConeThetaFamily_reindex
      j r q hq)

/-- The original square, with vertical normalization time and horizontal sum time. -/
def perfectOpenScalarSumNormalizationSquareMap :
    (SSet.diagonalSSet S ⊗ Δ[1]) ⊗ Δ[1] ⟶ SSet.diagonalSSet (bisimplicialSSet W) :=
  weakGridFamilySquare W (perfectOpenScalarZeroSumMap j) (perfectOpenScalarConeSumMap j r)
    (perfectOpenScalarZeroPairMap j) (perfectOpenScalarConePairMap j r q hq)
    (perfectOpenScalarSeparatedSumFamily j r q hq)
    (perfectOpenScalarCanonicalSumFamily j r q hq)
    (perfectOpenScalarZeroThetaFamily j) (perfectOpenScalarConeThetaFamily j r q hq)
    (perfectOpenScalarSumNormalizationFamilySquare j r q hq)
    (perfectOpenScalarSeparatedSumFamily_weak j r q hq)
    (perfectOpenScalarCanonicalSumFamily_weak j r q hq)
    (perfectOpenScalarZeroThetaFamily_weak j) (perfectOpenScalarConeThetaFamily_weak j r q hq)
    (perfectOpenScalarSeparatedSumFamily_reindex j r q hq)
    (perfectOpenScalarCanonicalSumFamily_reindex j r q hq)
    (perfectOpenScalarZeroThetaFamily_reindex j) (perfectOpenScalarConeThetaFamily_reindex j r q hq)

/-- The entire vertical zero face is its precise original weak-grid cylinder. -/
theorem perfectOpenScalarSumNormalizationSquareMap_vertical_zero :
    SSet.ι₀ ≫ perfectOpenScalarSumNormalizationSquareMap j r q hq =
      (perfectOpenScalarSumDiagonalHomotopy j r q hq).h :=
  weakGridFamilySquare_vertical_zero W (perfectOpenScalarZeroSumMap j)
      (perfectOpenScalarConeSumMap j r)
    (perfectOpenScalarZeroPairMap j) (perfectOpenScalarConePairMap j r q hq)
    (perfectOpenScalarSeparatedSumFamily j r q hq)
    (perfectOpenScalarCanonicalSumFamily j r q hq)
    (perfectOpenScalarZeroThetaFamily j) (perfectOpenScalarConeThetaFamily j r q hq)
    (perfectOpenScalarSumNormalizationFamilySquare j r q hq)
    (perfectOpenScalarSeparatedSumFamily_weak j r q hq)
    (perfectOpenScalarCanonicalSumFamily_weak j r q hq)
    (perfectOpenScalarZeroThetaFamily_weak j) (perfectOpenScalarConeThetaFamily_weak j r q hq)
    (perfectOpenScalarSeparatedSumFamily_reindex j r q hq)
    (perfectOpenScalarCanonicalSumFamily_reindex j r q hq)
    (perfectOpenScalarZeroThetaFamily_reindex j) (perfectOpenScalarConeThetaFamily_reindex j r q hq)

/-- The entire vertical one face is its precise original weak-grid cylinder. -/
theorem perfectOpenScalarSumNormalizationSquareMap_vertical_one :
    SSet.ι₁ ≫ perfectOpenScalarSumNormalizationSquareMap j r q hq =
      (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq).h :=
  weakGridFamilySquare_vertical_one W (perfectOpenScalarZeroSumMap j)
      (perfectOpenScalarConeSumMap j r)
    (perfectOpenScalarZeroPairMap j) (perfectOpenScalarConePairMap j r q hq)
    (perfectOpenScalarSeparatedSumFamily j r q hq)
    (perfectOpenScalarCanonicalSumFamily j r q hq)
    (perfectOpenScalarZeroThetaFamily j) (perfectOpenScalarConeThetaFamily j r q hq)
    (perfectOpenScalarSumNormalizationFamilySquare j r q hq)
    (perfectOpenScalarSeparatedSumFamily_weak j r q hq)
    (perfectOpenScalarCanonicalSumFamily_weak j r q hq)
    (perfectOpenScalarZeroThetaFamily_weak j) (perfectOpenScalarConeThetaFamily_weak j r q hq)
    (perfectOpenScalarSeparatedSumFamily_reindex j r q hq)
    (perfectOpenScalarCanonicalSumFamily_reindex j r q hq)
    (perfectOpenScalarZeroThetaFamily_reindex j) (perfectOpenScalarConeThetaFamily_reindex j r q hq)

/-- The entire horizontal zero face is its precise original weak-grid cylinder. -/
theorem perfectOpenScalarSumNormalizationSquareMap_horizontal_zero :
    (SSet.ι₀ ▷ Δ[1]) ≫ perfectOpenScalarSumNormalizationSquareMap j r q hq =
      (perfectOpenScalarZeroThetaCoarseDiagonalHomotopy j).h :=
  weakGridFamilySquare_horizontal_zero W (perfectOpenScalarZeroSumMap j)
      (perfectOpenScalarConeSumMap j r)
    (perfectOpenScalarZeroPairMap j) (perfectOpenScalarConePairMap j r q hq)
    (perfectOpenScalarSeparatedSumFamily j r q hq)
    (perfectOpenScalarCanonicalSumFamily j r q hq)
    (perfectOpenScalarZeroThetaFamily j) (perfectOpenScalarConeThetaFamily j r q hq)
    (perfectOpenScalarSumNormalizationFamilySquare j r q hq)
    (perfectOpenScalarSeparatedSumFamily_weak j r q hq)
    (perfectOpenScalarCanonicalSumFamily_weak j r q hq)
    (perfectOpenScalarZeroThetaFamily_weak j) (perfectOpenScalarConeThetaFamily_weak j r q hq)
    (perfectOpenScalarSeparatedSumFamily_reindex j r q hq)
    (perfectOpenScalarCanonicalSumFamily_reindex j r q hq)
    (perfectOpenScalarZeroThetaFamily_reindex j) (perfectOpenScalarConeThetaFamily_reindex j r q hq)

/-- The entire horizontal one face is its precise original weak-grid cylinder. -/
theorem perfectOpenScalarSumNormalizationSquareMap_horizontal_one :
    (SSet.ι₁ ▷ Δ[1]) ≫ perfectOpenScalarSumNormalizationSquareMap j r q hq =
      (perfectOpenScalarConeThetaCoarseDiagonalHomotopy j r q hq).h :=
  weakGridFamilySquare_horizontal_one W (perfectOpenScalarZeroSumMap j)
      (perfectOpenScalarConeSumMap j r)
    (perfectOpenScalarZeroPairMap j) (perfectOpenScalarConePairMap j r q hq)
    (perfectOpenScalarSeparatedSumFamily j r q hq)
    (perfectOpenScalarCanonicalSumFamily j r q hq)
    (perfectOpenScalarZeroThetaFamily j) (perfectOpenScalarConeThetaFamily j r q hq)
    (perfectOpenScalarSumNormalizationFamilySquare j r q hq)
    (perfectOpenScalarSeparatedSumFamily_weak j r q hq)
    (perfectOpenScalarCanonicalSumFamily_weak j r q hq)
    (perfectOpenScalarZeroThetaFamily_weak j) (perfectOpenScalarConeThetaFamily_weak j r q hq)
    (perfectOpenScalarSeparatedSumFamily_reindex j r q hq)
    (perfectOpenScalarCanonicalSumFamily_reindex j r q hq)
    (perfectOpenScalarZeroThetaFamily_reindex j) (perfectOpenScalarConeThetaFamily_reindex j r q hq)

/-- Every cut in both original cylinder directions fixes the actual chosen-zero simplex. -/
theorem perfectOpenScalarSumNormalizationSquareMap_fixed_zero :
    ((SSet.yonedaEquiv.symm (subdivisionZeroVertex V) ▷ Δ[1]) ▷ Δ[1]) ≫
        perfectOpenScalarSumNormalizationSquareMap j r q hq =
      CartesianMonoidalCategory.fst (Δ[0] ⊗ Δ[1]) Δ[1] ≫
        CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫
          SSet.yonedaEquiv.symm (diagonalZeroVertex W) := by
  refine weakGridFamilySquare_fixed_vertex W (perfectOpenScalarZeroSumMap j)
      (perfectOpenScalarConeSumMap j r)
    (perfectOpenScalarZeroPairMap j) (perfectOpenScalarConePairMap j r q hq)
    (perfectOpenScalarSeparatedSumFamily j r q hq)
    (perfectOpenScalarCanonicalSumFamily j r q hq)
    (perfectOpenScalarZeroThetaFamily j) (perfectOpenScalarConeThetaFamily j r q hq)
    (perfectOpenScalarSumNormalizationFamilySquare j r q hq)
    (perfectOpenScalarSeparatedSumFamily_weak j r q hq)
    (perfectOpenScalarCanonicalSumFamily_weak j r q hq)
    (perfectOpenScalarZeroThetaFamily_weak j) (perfectOpenScalarConeThetaFamily_weak j r q hq)
    (perfectOpenScalarSeparatedSumFamily_reindex j r q hq)
    (perfectOpenScalarCanonicalSumFamily_reindex j r q hq)
    (perfectOpenScalarZeroThetaFamily_reindex j) (perfectOpenScalarConeThetaFamily_reindex j r q hq)
    (subdivisionZeroVertex V) ?_ ?_ ?_ ?_
  · intro n z p
    exact normalizedSumGrid_zero_obj V W (h0w).exactH (h0w).exactF p
  · intro n z p
    exact normalizedSumGrid_zero_obj V W (h1w).exactH (h1w).exactF p
  · intro n z p
    exact perfectOpenScalarZeroPairTarget_zero j
  · intro n z p
    exact perfectOpenScalarConePairTarget_zero j r q hq

/-- The double-cylinder realization retains both independent times and original input. -/
def perfectOpenScalarSumNormalizationRealizationSquare :
    C(unitInterval × (unitInterval × |SSet.diagonalSSet S|),
      |SSet.diagonalSSet (bisimplicialSSet W)|) :=
  realizationDoubleCylinderSquare (perfectOpenScalarSumNormalizationSquareMap j r q hq)

/-- The square uses exactly the two original realization-cylinder inverses, in their old order. -/
theorem perfectOpenScalarSumNormalizationRealizationSquare_apply (t s : unitInterval)
    (x : |SSet.diagonalSSet S|) :
    perfectOpenScalarSumNormalizationRealizationSquare j r q hq (t, (s, x)) =
      SSet.toTop.map (perfectOpenScalarSumNormalizationSquareMap j r q hq)
        ((realizationCylinderIso (SSet.diagonalSSet S ⊗ Δ[1])).inv
          ((realizationCylinderIso (SSet.diagonalSSet S)).inv
            (x, ULift.up s), ULift.up t)) := rfl

/-- The complete realized vertical zero face retains its actual original cylinder. -/
theorem perfectOpenScalarSumNormalizationRealizationSquare_vertical_zero (t : unitInterval)
    (x : |SSet.diagonalSSet S|) :
    perfectOpenScalarSumNormalizationRealizationSquare j r q hq (0, (t, x)) =
      realizationSimplicialHomotopy (perfectOpenScalarSumDiagonalHomotopy j r q hq) (t, x) :=
  realizationDoubleCylinderSquare_vertical_zero
    (perfectOpenScalarSumNormalizationSquareMap j r q hq)
    (perfectOpenScalarSumDiagonalHomotopy j r q hq)
    (perfectOpenScalarSumNormalizationSquareMap_vertical_zero j r q hq) t x

/-- The complete realized vertical one face retains its actual original cylinder. -/
theorem perfectOpenScalarSumNormalizationRealizationSquare_vertical_one (t : unitInterval)
    (x : |SSet.diagonalSSet S|) :
    perfectOpenScalarSumNormalizationRealizationSquare j r q hq (1, (t, x)) =
      realizationSimplicialHomotopy (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq)
      (t, x) :=
  realizationDoubleCylinderSquare_vertical_one
    (perfectOpenScalarSumNormalizationSquareMap j r q hq)
    (perfectOpenScalarCanonicalSumDiagonalHomotopy j r q hq)
    (perfectOpenScalarSumNormalizationSquareMap_vertical_one j r q hq) t x

/-- The complete realized horizontal zero face retains its actual original cylinder. -/
theorem perfectOpenScalarSumNormalizationRealizationSquare_horizontal_zero (t : unitInterval)
    (x : |SSet.diagonalSSet S|) :
    perfectOpenScalarSumNormalizationRealizationSquare j r q hq (t, (0, x)) =
      realizationSimplicialHomotopy (perfectOpenScalarZeroThetaCoarseDiagonalHomotopy j) (t, x) :=
  realizationDoubleCylinderSquare_horizontal_zero
    (perfectOpenScalarSumNormalizationSquareMap j r q hq)
    (perfectOpenScalarZeroThetaCoarseDiagonalHomotopy j)
    (perfectOpenScalarSumNormalizationSquareMap_horizontal_zero j r q hq) t x

/-- The complete realized horizontal one face retains its actual original cylinder. -/
theorem perfectOpenScalarSumNormalizationRealizationSquare_horizontal_one (t : unitInterval)
    (x : |SSet.diagonalSSet S|) :
    perfectOpenScalarSumNormalizationRealizationSquare j r q hq (t, (1, x)) =
      realizationSimplicialHomotopy (perfectOpenScalarConeThetaCoarseDiagonalHomotopy j r q
      hq) (t, x) :=
  realizationDoubleCylinderSquare_horizontal_one
    (perfectOpenScalarSumNormalizationSquareMap j r q hq)
    (perfectOpenScalarConeThetaCoarseDiagonalHomotopy j r q hq)
    (perfectOpenScalarSumNormalizationSquareMap_horizontal_one j r q hq) t x

/-- Every pair of times fixes the whole original chosen-zero surface. -/
theorem perfectOpenScalarSumNormalizationRealizationSquare_fixed_zero (t s : unitInterval) :
    perfectOpenScalarSumNormalizationRealizationSquare j r q hq
      (t, (s, subdivisionBasepoint V)) = realizationPoint (diagonalZeroVertex W) :=
  realizationDoubleCylinderSquare_fixed_vertex
    (perfectOpenScalarSumNormalizationSquareMap j r q hq)
    (subdivisionZeroVertex V) (diagonalZeroVertex W)
    (perfectOpenScalarSumNormalizationSquareMap_fixed_zero j r q hq) t s

/-- The same complete zero normalization cylinder is already fine weak. -/
def perfectOpenScalarZeroThetaDiagonalHomotopy :
    SSet.Homotopy
      (SSet.diagonalMap (normalizedSumMap V V (h0f).exactH (h0f).exactF))
      (SSet.diagonalMap (separatedPairMap V ≫
        bisimplicialSSetMap (productStructure V V).cof (productStructure V V).weq
          (perfectOpenScalarZeroPairTarget_exact j))) :=
  diagonalWeakGridHomotopy V _ _
    (fun _ _ A ↦ whiskerLeft (separatedPairGrid A.1) (perfectOpenScalarZeroSumNormalizationIso
      j).hom)
    (fun _ _ _ _ ↦ (V).weq_iso _ inferInstance)
    (fun {_ _} ρ A x ↦ scalarSumFamily_reindex (perfectOpenScalarZeroSumNormalizationIso
      j).hom ρ A x)

/-- The entire fine zero cylinder maps to the coarse cylinder with the same actual data. -/
theorem perfectOpenScalarZeroThetaDiagonalHomotopy_changeWeak :
    (perfectOpenScalarZeroThetaDiagonalHomotopy j).h ≫
        SSet.diagonalMap (bisimplicialSSetMap (V).cof (V).weq
          (changeWeak_exact (perfectOpenNested j))) =
      (perfectOpenScalarZeroThetaCoarseDiagonalHomotopy j).h := by
  ext n z
  apply Subtype.ext
  change nerveCylinderDiagram
      (whiskerLeft (separatedPairGrid z.1.1) (perfectOpenScalarZeroSumNormalizationIso j).hom)
      z.2.down ⋙ 𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
        X.toRingedSpace))) =
    nerveCylinderDiagram
      (whiskerLeft (separatedPairGrid z.1.1) (perfectOpenScalarZeroSumNormalizationIso j).hom)
      z.2.down
  exact Functor.comp_id _

/-- The full fine zero normalization time fixes the actual subdivided zero point. -/
theorem perfectOpenScalarZeroThetaDiagonalHomotopy_fixed_zero (t : unitInterval) :
    realizationSimplicialHomotopy (perfectOpenScalarZeroThetaDiagonalHomotopy j)
      (t, subdivisionBasepoint V) = realizationPoint (diagonalZeroVertex V) := by
  refine diagonalWeakGridRealizationHomotopy_fixed_vertex V
    (normalizedSumMap V V (h0f).exactH (h0f).exactF)
    (separatedPairMap V ≫ bisimplicialSSetMap
      (productStructure V V).cof (productStructure V V).weq
      (perfectOpenScalarZeroPairTarget_exact j))
    (fun _ _ A ↦ whiskerLeft (separatedPairGrid A.1) (perfectOpenScalarZeroSumNormalizationIso
      j).hom)
    (fun _ _ _ _ ↦ (V).weq_iso _ inferInstance)
    (fun {_ _} ρ A x ↦ scalarSumFamily_reindex (perfectOpenScalarZeroSumNormalizationIso
      j).hom ρ A x)
    (subdivisionZeroVertex V) ?_ ?_ t
  · intro n z p
    exact normalizedSumGrid_zero_obj V V (h0f).exactH (h0f).exactF p
  · intro n z p
    exact perfectOpenScalarZeroPairTarget_zero j

/-- Both time and input are retained by the actual ordinary change-weak map. -/
theorem perfectOpenScalarZeroThetaRealization_changeWeak (t : unitInterval)
    (x : |SSet.diagonalSSet S|) :
    deloopingMap (changeWeak_exact (perfectOpenNested j))
        (SSet.toTop.map (bisimplicialDiagonalIso V).hom
          (realizationSimplicialHomotopy (perfectOpenScalarZeroThetaDiagonalHomotopy j)
            (t, x))) =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy
          (perfectOpenScalarZeroThetaCoarseDiagonalHomotopy j) (t, x)) := by
  have hc := realizationSimplicialHomotopy_naturality
    (perfectOpenScalarZeroThetaDiagonalHomotopy j)
    (perfectOpenScalarZeroThetaCoarseDiagonalHomotopy j) (𝟙 _)
    (SSet.diagonalMap (bisimplicialSSetMap (V).cof (V).weq
      (changeWeak_exact (perfectOpenNested j))))
    (by simpa only [id_whiskerRight, Category.id_comp] using
      perfectOpenScalarZeroThetaDiagonalHomotopy_changeWeak j) t x
  rw [SSet.toTop.map_id] at hc
  simp only [TopCat.id_app] at hc
  have hn := DFunLike.congr_fun
    (realizedDiagonalMap_exact_naturality V W (changeWeak_exact (perfectOpenNested j)))
    (realizationSimplicialHomotopy (perfectOpenScalarZeroThetaDiagonalHomotopy j) (t, x))
  exact hn.symm.trans (congrArg
    (fun y ↦ SSet.toTop.map (bisimplicialDiagonalIso W).hom y) hc)

/-- The same complete cone normalization cylinder is already fine weak. -/
def perfectOpenScalarConeThetaDiagonalHomotopy :
    SSet.Homotopy
      (SSet.diagonalMap (normalizedSumMap V V (h1f).exactH (h1f).exactF))
      (SSet.diagonalMap (separatedPairMap V ≫
        bisimplicialSSetMap (productStructure V V).cof (productStructure V V).weq
          (perfectOpenScalarConePairTarget_exact j r q hq))) :=
  diagonalWeakGridHomotopy V _ _
    (fun _ _ A ↦ whiskerLeft (separatedPairGrid A.1) (perfectOpenScalarConeSumNormalizationIso
      j r q hq).hom)
    (fun _ _ _ _ ↦ (V).weq_iso _ inferInstance)
    (fun {_ _} ρ A x ↦ scalarSumFamily_reindex (perfectOpenScalarConeSumNormalizationIso j r q
      hq).hom ρ A x)

/-- The entire fine cone cylinder maps to the coarse cylinder with the same actual data. -/
theorem perfectOpenScalarConeThetaDiagonalHomotopy_changeWeak :
    (perfectOpenScalarConeThetaDiagonalHomotopy j r q hq).h ≫
        SSet.diagonalMap (bisimplicialSSetMap (V).cof (V).weq
          (changeWeak_exact (perfectOpenNested j))) =
      (perfectOpenScalarConeThetaCoarseDiagonalHomotopy j r q hq).h := by
  ext n z
  apply Subtype.ext
  change nerveCylinderDiagram
      (whiskerLeft (separatedPairGrid z.1.1) (perfectOpenScalarConeSumNormalizationIso j r q
      hq).hom) z.2.down ⋙ 𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
        X.toRingedSpace))) =
    nerveCylinderDiagram
      (whiskerLeft (separatedPairGrid z.1.1) (perfectOpenScalarConeSumNormalizationIso j r q
      hq).hom) z.2.down
  exact Functor.comp_id _

/-- The full fine cone normalization time fixes the actual subdivided zero point. -/
theorem perfectOpenScalarConeThetaDiagonalHomotopy_fixed_zero (t : unitInterval) :
    realizationSimplicialHomotopy (perfectOpenScalarConeThetaDiagonalHomotopy j r q hq)
      (t, subdivisionBasepoint V) = realizationPoint (diagonalZeroVertex V) := by
  refine diagonalWeakGridRealizationHomotopy_fixed_vertex V
    (normalizedSumMap V V (h1f).exactH (h1f).exactF)
    (separatedPairMap V ≫ bisimplicialSSetMap
      (productStructure V V).cof (productStructure V V).weq
      (perfectOpenScalarConePairTarget_exact j r q hq))
    (fun _ _ A ↦ whiskerLeft (separatedPairGrid A.1) (perfectOpenScalarConeSumNormalizationIso
      j r q hq).hom)
    (fun _ _ _ _ ↦ (V).weq_iso _ inferInstance)
    (fun {_ _} ρ A x ↦ scalarSumFamily_reindex (perfectOpenScalarConeSumNormalizationIso j r q
      hq).hom ρ A x)
    (subdivisionZeroVertex V) ?_ ?_ t
  · intro n z p
    exact normalizedSumGrid_zero_obj V V (h1f).exactH (h1f).exactF p
  · intro n z p
    exact perfectOpenScalarConePairTarget_zero j r q hq

/-- Both time and input are retained by the actual ordinary change-weak map. -/
theorem perfectOpenScalarConeThetaRealization_changeWeak (t : unitInterval)
    (x : |SSet.diagonalSSet S|) :
    deloopingMap (changeWeak_exact (perfectOpenNested j))
        (SSet.toTop.map (bisimplicialDiagonalIso V).hom
          (realizationSimplicialHomotopy (perfectOpenScalarConeThetaDiagonalHomotopy j r q hq)
            (t, x))) =
      SSet.toTop.map (bisimplicialDiagonalIso W).hom
        (realizationSimplicialHomotopy
          (perfectOpenScalarConeThetaCoarseDiagonalHomotopy j r q hq) (t, x)) := by
  have hc := realizationSimplicialHomotopy_naturality
    (perfectOpenScalarConeThetaDiagonalHomotopy j r q hq)
    (perfectOpenScalarConeThetaCoarseDiagonalHomotopy j r q hq) (𝟙 _)
    (SSet.diagonalMap (bisimplicialSSetMap (V).cof (V).weq
      (changeWeak_exact (perfectOpenNested j))))
    (by simpa only [id_whiskerRight, Category.id_comp] using
      perfectOpenScalarConeThetaDiagonalHomotopy_changeWeak j r q hq) t x
  rw [SSet.toTop.map_id] at hc
  simp only [TopCat.id_app] at hc
  have hn := DFunLike.congr_fun
    (realizedDiagonalMap_exact_naturality V W (changeWeak_exact (perfectOpenNested j)))
    (realizationSimplicialHomotopy (perfectOpenScalarConeThetaDiagonalHomotopy j r q hq) (t, x))
  exact hn.symm.trans (congrArg
    (fun y ↦ SSet.toTop.map (bisimplicialDiagonalIso W).hom y) hc)

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0317",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberSumNormalizationSquare.lean:34-557"
    "adaptation"
    "Actual scalar normalization and canonical fiber maps on the unchanged subdivision cube"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarConeThetaDiagonalHomotopy_changeWeak
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarConeThetaDiagonalHomotopy_fixed_zero
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarConeThetaRealization_changeWeak
