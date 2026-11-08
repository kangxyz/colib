/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberCubeSquare
public import Colib.KTheory.Waldhausen.Additivity.ChangeWeakBasedHomotopy
public import Colib.KTheory.Waldhausen.Additivity.DiagonalNaturality

/-! # Original fine additivity edges of the scalar cube square

The two old fine paths retain every time and spatial coordinate. Their whole change-weak
images determine all four endpoint casts before the original boundary interpolation is cast.
The fine projection and normalized canonical-sum endpoint are separate consumers.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberFineCubeEdges.lean:37-292`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native ownership preserves the
actual chosen zero, normalizations, cylinder coordinates, maps and orientations. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
  CategoryTheory.Waldhausen.Fibration
open SSet
open scoped Simplicial Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules

local instance fineCubeCoproducts (X : Scheme.{u}) : HasBinaryCoproducts
  (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :=
  Additivity.hasBinaryCoproducts (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)

section FinePath
variable (X : Scheme.{u})
  {F G H : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) ⥤
    ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))}
  (a : F ⟶ G) (b : G ⟶ H)
  (hs : IsCofibrationSequence (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace) a b)
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace

/-- The original fine middle endpoint after the actual horizontal and diagonal maps. -/
def scalarFineAdditivitySourceMap :
    C(|SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|,
      (V).Delooping) :=
  (SSet.toTop.map (bisimplicialDiagonalIso V).hom).hom.comp
    ((realizedDiagonalMap (bisimplicialSSetMap (V).cof (V).weq hs.exactG.rebase)).comp
      (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V))))

/-- The original quotient-first separated endpoint after the actual diagonal map. -/
def scalarFineAdditivityTargetMap :
    C(|SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V)|,
      (V).Delooping) :=
  (SSet.toTop.map (bisimplicialDiagonalIso V).hom).hom.comp
    (realizedDiagonalMap (normalizedSumMap V V hs.exactH hs.exactF))

/-- The same fine based additivity homotopy, postcomposed only by the original diagonal. -/
def scalarFineAdditivityHomotopy :
    (scalarFineAdditivitySourceMap X a b hs).HomotopyRel
      (scalarFineAdditivityTargetMap X a b hs) {subdivisionBasepoint V} :=
  (subdividedBasedAdditivityHomotopy V V a b hs).compContinuousMap
    (SSet.toTop.map (bisimplicialDiagonalIso V).hom).hom

/-- The source map retains the actual chosen zero through both original comparisons. -/
theorem scalarFineAdditivitySourceMap_basepoint :
    scalarFineAdditivitySourceMap X a b hs (subdivisionBasepoint V) = (V).kBasepoint :=
  (congrArg (fun y ↦ SSet.toTop.map (bisimplicialDiagonalIso V).hom y)
    ((congrArg (realizedDiagonalMap (bisimplicialSSetMap (V).cof (V).weq hs.exactG.rebase))
      (horizontalEndpoint_basepoint V)).trans
        (rebasedDiagonalMap_basepoint V V hs.exactG))).trans
    (diagonalRealization_basepoint V)

/-- Every time of the original fine path fixes the full chosen-zero input. -/
theorem scalarFineAdditivityHomotopy_zero (t : unitInterval) :
    scalarFineAdditivityHomotopy X a b hs (t, subdivisionBasepoint V) = (V).kBasepoint :=
  ((scalarFineAdditivityHomotopy X a b hs).eq_fst t (Set.mem_singleton _)).trans
    (scalarFineAdditivitySourceMap_basepoint X a b hs)

/-- The separated endpoint is based by the same entire original zero track. -/
theorem scalarFineAdditivityTargetMap_basepoint :
    scalarFineAdditivityTargetMap X a b hs (subdivisionBasepoint V) = (V).kBasepoint :=
  ((scalarFineAdditivityHomotopy X a b hs).apply_one _).symm.trans
    (scalarFineAdditivityHomotopy_zero X a b hs 1)

variable (n : ℕ) (p : GenLoop (Fin (n + 1))
  |SSet.diagonalSSet
    (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (RingedSpace.perfectComplexesWaldhausen
      X.toRingedSpace))|
  (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)))

/-- The original fine middle endpoint evaluated on the unchanged subdivision cube. -/
def scalarFineAdditivitySourceCube : GenLoop (Fin (n + 1)) (V).Delooping (V).kBasepoint :=
  GenLoop.postcomp (scalarFineAdditivitySourceMap X a b hs)
    (scalarFineAdditivitySourceMap_basepoint X a b hs) p

/-- The original separated endpoint evaluated on that same subdivision cube. -/
def scalarFineAdditivityTargetCube : GenLoop (Fin (n + 1)) (V).Delooping (V).kBasepoint :=
  GenLoop.postcomp (scalarFineAdditivityTargetMap X a b hs)
    (scalarFineAdditivityTargetMap_basepoint X a b hs) p

/-- Curry the old entire fine homotopy using the existing generalized-loop path construction. -/
def scalarFineAdditivityCubePath :
    Path (scalarFineAdditivitySourceCube X a b hs n p)
      (scalarFineAdditivityTargetCube X a b hs n p) :=
  genLoopPathOfHomotopyRel (GenLoop.postcompHomotopy
    (scalarFineAdditivitySourceMap_basepoint X a b hs)
    (scalarFineAdditivityTargetMap_basepoint X a b hs)
    (scalarFineAdditivityHomotopy X a b hs).toHomotopy
    (scalarFineAdditivityHomotopy_zero X a b hs) p)

/-- Every path time and spatial coordinate is the original fine additivity parameter. -/
theorem scalarFineAdditivityCubePath_apply (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    scalarFineAdditivityCubePath X a b hs n p t z =
      SSet.toTop.map (bisimplicialDiagonalIso V).hom
        (subdividedBasedAdditivityHomotopy V V a b hs (t, p z)) := rfl
end FinePath

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)

/-- Fine and coarse structures use the same actual chosen zero object. -/
theorem perfectOpenScalarFineZero_eq : (V).zero = (W).zero := rfl

/-- The identity quotient is the same actual chosen-zero natural transformation. -/
theorem perfectOpenScalarFineZeroArrow_eq :
    QuotientRows.oneIdToZero V = QuotientRows.oneIdToZero W := rfl

/-- The literal fine identity-to-chosen-zero cofibration sequence. -/
theorem perfectScalarIdentityFineCofibrationSequence :
    IsCofibrationSequence V V
      (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
      (QuotientRows.oneIdToZero V) :=
  identityCofibrationSequence V
    (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))))
    V (IsExact.id (V).cof (V).weq)

variable (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
  (n : ℕ) (p : GenLoop (Fin (n + 1))
    |SSet.diagonalSSet
      (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet (RingedSpace.perfectComplexesWaldhausen
        X.toRingedSpace))|
    (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)))

/-- The actual fine-to-coarse map on the original generalized-loop spaces. -/
def perfectOpenScalarCubeChangeWeak :
    C(GenLoop (Fin (n + 1)) (V).Delooping (V).kBasepoint,
      GenLoop (Fin (n + 1)) (W).Delooping (W).kBasepoint) :=
  genLoopPostcompContinuousMap (changeWeakMap (perfectOpenNested j))
    (changeWeakMap_basepoint (perfectOpenNested j))

/-- The unchanged fine identity-sequence additivity path. -/
def perfectOpenScalarIdentityFineCubePath :=
  scalarFineAdditivityCubePath X (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
    (X := X.toRingedSpace))))) (QuotientRows.oneIdToZero V)
    (perfectScalarIdentityFineCofibrationSequence (X := X)) n p

/-- The unchanged fine scalar-cylinder additivity path with its literal cone quotient. -/
def perfectOpenScalarSequenceFineCubePath :=
  scalarFineAdditivityCubePath X (perfectScalarInclusionNat X r)
    (perfectScalarConeProjectionNat X r) (perfectScalarCofibrationSequence X r) n p

/-- Whole fine identity path image, before any endpoint casts are introduced. -/
theorem perfectOpenScalarIdentityFineCubePath_changeWeak (t : unitInterval) :
    perfectOpenScalarCubeChangeWeak j n
        (perfectOpenScalarIdentityFineCubePath n p t) =
      perfectOpenScalarCofiberCubeIdentityPath j r q hq n p t := by
  ext z
  have hd := DFunLike.congr_fun
    (realizedDiagonalMap_exact_naturality V W (changeWeak_exact (perfectOpenNested j)))
    (subdividedBasedAdditivityHomotopy V V (𝟙 (𝟭 (ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
      (QuotientRows.oneIdToZero V) (perfectScalarIdentityFineCofibrationSequence (X := X))
      (t, p z))
  have hc := subdividedBasedAdditivityHomotopy_changeWeak V V (perfectOpenNested j)
    (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
      (QuotientRows.oneIdToZero V)
    (perfectScalarIdentityFineCofibrationSequence (X := X)) t (p z)
  exact hd.symm.trans ((congrArg
    (fun y ↦ SSet.toTop.map (bisimplicialDiagonalIso W).hom y) hc).trans
      ((perfectOpenScalarCofiberCubeSquare_transformation_zero j r q hq n p t z).symm))

/-- Whole fine scalar path image, retaining the original change-weak cofibration sequence. -/
theorem perfectOpenScalarSequenceFineCubePath_changeWeak (t : unitInterval) :
    perfectOpenScalarCubeChangeWeak j n
        (perfectOpenScalarSequenceFineCubePath r n p t) =
      perfectOpenScalarCofiberCubeScalarPath j r q hq n p t := by
  ext z
  have hd := DFunLike.congr_fun
    (realizedDiagonalMap_exact_naturality V W (changeWeak_exact (perfectOpenNested j)))
    (subdividedBasedAdditivityHomotopy V V (perfectScalarInclusionNat X r)
      (perfectScalarConeProjectionNat X r) (perfectScalarCofibrationSequence X r) (t, p z))
  have hc := subdividedBasedAdditivityHomotopy_changeWeak V V (perfectOpenNested j)
    (perfectScalarInclusionNat X r) (perfectScalarConeProjectionNat X r)
    (perfectScalarCofibrationSequence X r) t (p z)
  exact hd.symm.trans ((congrArg
    (fun y ↦ SSet.toTop.map (bisimplicialDiagonalIso W).hom y) hc).trans
      ((perfectOpenScalarCofiberCubeSquare_transformation_one j r q hq n p t z).symm))

/-- Corner 00 is derived from the whole unchanged fine edge. -/
theorem perfectOpenScalarFineCorner00 :
    perfectOpenScalarCubeChangeWeak j n
      (scalarFineAdditivitySourceCube X (𝟙 (𝟭 (ObjectProperty.FullSubcategory
        (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))))) (QuotientRows.oneIdToZero V)
      (perfectScalarIdentityFineCofibrationSequence (X := X)) n p) =
      perfectOpenScalarCofiberCubeSquare j r q hq n p (0, 0) :=
  (congrArg (perfectOpenScalarCubeChangeWeak j n)
    (perfectOpenScalarIdentityFineCubePath n p).source).symm.trans
    ((perfectOpenScalarIdentityFineCubePath_changeWeak j r q hq n p 0).trans
      (perfectOpenScalarCofiberCubeIdentityPath j r q hq n p).source)

/-- Corner 01 is derived from the whole unchanged fine edge. -/
theorem perfectOpenScalarFineCorner01 :
    perfectOpenScalarCubeChangeWeak j n
      (scalarFineAdditivityTargetCube X (𝟙 (𝟭 (ObjectProperty.FullSubcategory
        (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))))) (QuotientRows.oneIdToZero V)
      (perfectScalarIdentityFineCofibrationSequence (X := X)) n p) =
      perfectOpenScalarCofiberCubeSquare j r q hq n p (0, 1) :=
  (congrArg (perfectOpenScalarCubeChangeWeak j n)
    (perfectOpenScalarIdentityFineCubePath n p).target).symm.trans
    ((perfectOpenScalarIdentityFineCubePath_changeWeak j r q hq n p 1).trans
      (perfectOpenScalarCofiberCubeIdentityPath j r q hq n p).target)

/-- Corner 10 is derived from the whole unchanged fine edge. -/
theorem perfectOpenScalarFineCorner10 :
    perfectOpenScalarCubeChangeWeak j n
      (scalarFineAdditivitySourceCube X (perfectScalarInclusionNat X r)
      (perfectScalarConeProjectionNat X r) (perfectScalarCofibrationSequence X r) n p) =
      perfectOpenScalarCofiberCubeSquare j r q hq n p (1, 0) :=
  (congrArg (perfectOpenScalarCubeChangeWeak j n)
    (perfectOpenScalarSequenceFineCubePath r n p).source).symm.trans
    ((perfectOpenScalarSequenceFineCubePath_changeWeak j r q hq n p 0).trans
      (perfectOpenScalarCofiberCubeScalarPath j r q hq n p).source)

/-- Corner 11 is derived from the whole unchanged fine edge. -/
theorem perfectOpenScalarFineCorner11 :
    perfectOpenScalarCubeChangeWeak j n
      (scalarFineAdditivityTargetCube X (perfectScalarInclusionNat X r)
      (perfectScalarConeProjectionNat X r) (perfectScalarCofibrationSequence X r) n p) =
      perfectOpenScalarCofiberCubeSquare j r q hq n p (1, 1) :=
  (congrArg (perfectOpenScalarCubeChangeWeak j n)
    (perfectOpenScalarSequenceFineCubePath r n p).target).symm.trans
    ((perfectOpenScalarSequenceFineCubePath_changeWeak j r q hq n p 1).trans
      (perfectOpenScalarCofiberCubeScalarPath j r q hq n p).target)

/-- The inclusion edge cast only by the four whole-path-derived corner equations. -/
def perfectOpenScalarFineCubeInclusionPath :=
  (perfectOpenScalarCofiberCubeInclusionPath j r q hq n p).cast
    (perfectOpenScalarFineCorner00 j r q hq n p) (perfectOpenScalarFineCorner10 j r q hq n p)

/-- The quotient-first sum edge with those same actual endpoint casts. -/
def perfectOpenScalarFineCubeSumPath :=
  (perfectOpenScalarCofiberCubeSumPath j r q hq n p).cast
    (perfectOpenScalarFineCorner01 j r q hq n p) (perfectOpenScalarFineCorner11 j r q hq n p)

/-- The entire cast identity edge is the actual mapped fine path. -/
theorem perfectOpenScalarIdentityFineCubePath_cast :
    (perfectOpenScalarCofiberCubeIdentityPath j r q hq n p).cast
        (perfectOpenScalarFineCorner00 j r q hq n p)
        (perfectOpenScalarFineCorner01 j r q hq n p) =
      (perfectOpenScalarIdentityFineCubePath n p).map
        (perfectOpenScalarCubeChangeWeak j n).continuous := by
  apply Path.ext
  funext t
  exact (perfectOpenScalarIdentityFineCubePath_changeWeak j r q hq n p t).symm

/-- The entire cast scalar edge is the actual mapped fine path. -/
theorem perfectOpenScalarSequenceFineCubePath_cast :
    (perfectOpenScalarCofiberCubeScalarPath j r q hq n p).cast
        (perfectOpenScalarFineCorner10 j r q hq n p)
        (perfectOpenScalarFineCorner11 j r q hq n p) =
      (perfectOpenScalarSequenceFineCubePath r n p).map
        (perfectOpenScalarCubeChangeWeak j n).continuous := by
  apply Path.ext
  funext t
  exact (perfectOpenScalarSequenceFineCubePath_changeWeak j r q hq n p t).symm

/-- The original oriented boundary interpolation with exactly the fine edge types. -/
def perfectOpenScalarFineCubeBoundaryHomotopy :
    ((perfectOpenScalarFineCubeInclusionPath j r q hq n p).trans
      ((perfectOpenScalarSequenceFineCubePath r n p).map
        (perfectOpenScalarCubeChangeWeak j n).continuous)).Homotopy
      (((perfectOpenScalarIdentityFineCubePath n p).map
        (perfectOpenScalarCubeChangeWeak j n).continuous).trans
        (perfectOpenScalarFineCubeSumPath j r q hq n p)) := by
  let J := (perfectOpenScalarCofiberCubeBoundaryHomotopy j r q hq n p).pathCast
    (perfectOpenScalarFineCorner00 j r q hq n p) (perfectOpenScalarFineCorner11 j r q hq n p)
  refine J.cast ?_ ?_
  · rw [Path.cast_trans _ _ _ (perfectOpenScalarFineCorner10 j r q hq n p) _,
      perfectOpenScalarSequenceFineCubePath_cast]
    rfl
  · rw [Path.cast_trans _ _ _ (perfectOpenScalarFineCorner01 j r q hq n p) _,
      perfectOpenScalarIdentityFineCubePath_cast]
    rfl

/-- Both interpolation times and every cube coordinate are the original square interpolation. -/
theorem perfectOpenScalarFineCubeBoundaryHomotopy_apply (a t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarFineCubeBoundaryHomotopy j r q hq n p (a, t) z =
      perfectOpenScalarCofiberCubeBoundaryHomotopy j r q hq n p (a, t) z := rfl

/-- The cast interpolation retains the entire spatial boundary for independently varying times. -/
theorem perfectOpenScalarFineCubeBoundaryHomotopy_boundary (a t : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarFineCubeBoundaryHomotopy j r q hq n p (a, t) z = (W).kBasepoint :=
  (perfectOpenScalarFineCubeBoundaryHomotopy j r q hq n p (a, t)).property z hz

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0316",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberFineCubeEdges.lean:154-292"
    "adaptation"
    "Actual fine edge images, derived corners, and the original cast boundary interpolation"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarIdentityFineCubePath_changeWeak
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarSequenceFineCubePath_changeWeak
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFineCorner00
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFineCorner01
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFineCorner10
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFineCorner11
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFineCubeBoundaryHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFineCubeBoundaryHomotopy_apply
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFineCubeBoundaryHomotopy_boundary
