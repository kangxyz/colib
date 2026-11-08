/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberFiberComparison
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberCubeReturnClass

/-! # Complete-signature checks of prescribed scalar return and canonical connecting maps -/
set_option autoImplicit false
set_option warningAsError true
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
open CategoryTheory.Waldhausen.Fibration SSet Topology
open scoped Simplicial Topology
universe u v
namespace ColibTest.ScalarReturnComparison

section Square
variable {X : Type u} [TopologicalSpace X] {E : Type v} [TopologicalSpace E]
  (f : C(E, X)) {a' b' c' d' : E}
  (A₀' : Path a' c') (A₁' : Path b' d') (P : Path b' a')
  {I' : Path (f a') (f b')} {Z' : Path (f c') (f d')}
open Path.Homotopy
/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
def original_squareProjectionReturnMap
    (J : (I'.trans (A₁'.map f.continuous)).Homotopy
      ((A₀'.map f.continuous).trans Z')) :
    (((P.symm.trans A₁').map f.continuous).trans
      (Z'.symm.trans (A₀'.map f.continuous).symm)).Homotopy
        (I'.trans (P.map f.continuous)).symm  :=
  squareProjectionReturnMap f A₀' A₁' P J

end Square

section Prefix
variable {X : Type u} [TopologicalSpace X] {x : X}
/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
theorem original_genLoopNormalizedSelfTrackPath_prefix (n : ℕ)
    (p : GenLoop (Fin (n + 1)) X x) (α : Path p p) :
    genLoopNormalizedSelfTrackPath n p α =
      (GenLoopPrefix.cancellation n p).symm.trans
        ((α.map (GenLoopPrefix.inversePrefix n p).continuous).trans
          (GenLoopPrefix.cancellation n p))  :=
  genLoopNormalizedSelfTrackPath_prefix n p α

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
theorem original_loopCurry_genLoopNormalizedSelfTrackCube_apply (n : ℕ)
    (p : GenLoop (Fin (n + 1)) X x) (α : Path p p)
    (z : Fin (n + 1) → unitInterval) (t : unitInterval) :
    loopCurry (genLoopNormalizedSelfTrackCube n p α) z t =
      genLoopNormalizedSelfTrackPath n p α t z  :=
  loopCurry_genLoopNormalizedSelfTrackCube_apply n p α z t

end Prefix

section Return
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (y : Y) (x : X) (h : f x = y) (n : ℕ)
local notation "E" => GenLoop (Fin (n + 1)) X x
local notation "F" => genLoopPostcompContinuousMap (N := Fin (n + 1)) f h
local notation "B" => (GenLoop.const : GenLoop (Fin (n + 1)) Y y)
open Topology.HomotopyFiber
/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
theorem original_genLoopReturnedLoop_prefix {a d : E} (R : Path a d) (lambda : Path (F d) (F a)) :
    genLoopReturnedLoop f y x h n (GenLoopPrefix.inversePrefix n a d)
        (genLoopPrefixNull f y x h n lambda) (genLoopPrefixReturn n R) =
      ((GenLoopPrefix.cancellation n (F a)).symm.trans
        ((R.map (F).continuous).map
          (GenLoopPrefix.inversePrefix n (F a)).continuous)).trans
        ((lambda.map (GenLoopPrefix.inversePrefix n (F a)).continuous).trans
          (GenLoopPrefix.cancellation n (F a)))  :=
  genLoopReturnedLoop_prefix f y x h n R lambda

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
def original_genLoopNormalizedReturnHomotopy {a d : E} (R : Path a d) (lambda : Path (F d) (F a)) :
    (genLoopNormalizedSelfTrackPath n (F a) ((R.map (F).continuous).trans lambda)).Homotopy
      (genLoopReturnedLoop f y x h n (GenLoopPrefix.inversePrefix n a d)
        (genLoopPrefixNull f y x h n lambda) (genLoopPrefixReturn n R))  :=
  genLoopNormalizedReturnHomotopy f y x h n R lambda

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
theorem original_genLoopNormalizedReturnHomotopy_boundary {a d : E}
    (R : Path a d) (lambda : Path (F d) (F a)) (s t : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    genLoopNormalizedReturnHomotopy f y x h n R lambda (s, t) z = y  :=
  genLoopNormalizedReturnHomotopy_boundary f y x h n R lambda s t z hz

end Return

section Scalar
local instance (X : Scheme.{u}) : HasBinaryCoproducts (ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :=
  Additivity.hasBinaryCoproducts (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
  (n : ℕ) (p : GenLoop (Fin (n + 1))
    |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙
      bisimplicialSSet (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|
    (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)))
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "N" => perfectOpenNested j
local notation "W" => NestedWeakEquivalences.coarse N
local notation "f" => changeWeakMap N
local notation "h" => changeWeakMap_basepoint N
local notation "F" => perfectOpenScalarCubeChangeWeak j n
local notation "af" => scalarFineAdditivitySourceCube X
  (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
  (QuotientRows.oneIdToZero V) (perfectScalarIdentityFineCofibrationSequence (X := X)) n p
local notation "df" => scalarFineAdditivityTargetCube X (perfectScalarInclusionNat X r)
  (perfectScalarConeProjectionNat X r) (perfectScalarCofibrationSequence X r) n p
local notation "b" => perfectOpenScalarCubeChangeWeak j n af
local notation "R" => perfectOpenScalarFineCubeReturn j r n p
local notation "lambda" => perfectOpenScalarFineCubeTerminalWord j r q hq n p
local notation "iota" => HomotopyFiber.loopInclusion f
  (Structure.kBasepoint W) (Structure.kBasepoint V) h
local notation "hiota" => HomotopyFiber.loopInclusion_refl f
  (Structure.kBasepoint W) (Structure.kBasepoint V) h
/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
def original_perfectOpenScalarFineCubeReturn : Path af df  :=
  perfectOpenScalarFineCubeReturn j r n p

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
def original_perfectOpenScalarFineCubeTerminalWord :
    Path (perfectOpenScalarCubeChangeWeak j n df) (perfectOpenScalarCubeChangeWeak j n af)  :=
  perfectOpenScalarFineCubeTerminalWord j r q hq n p

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
theorem original_perfectOpenScalarFineCubeReturn_eq :
    perfectOpenScalarFineCubeReturn j r n p =
      (perfectOpenScalarFineProjectionCubePath j r n p).symm.trans
        (perfectOpenScalarSequenceFineCubePath r n p)  :=
  perfectOpenScalarFineCubeReturn_eq j r n p

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
theorem original_perfectOpenScalarFineCubeTerminalWord_eq :
    perfectOpenScalarFineCubeTerminalWord j r q hq n p =
      (perfectOpenScalarFineCubeSumPath j r q hq n p).symm.trans
        ((perfectOpenScalarIdentityFineCubePath n p).map
          (perfectOpenScalarCubeChangeWeak j n).continuous).symm  :=
  perfectOpenScalarFineCubeTerminalWord_eq j r q hq n p

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
def original_perfectOpenScalarCubeReturnHomotopy :
    (((perfectOpenScalarFineCubeReturn j r n p).map
      (perfectOpenScalarCubeChangeWeak j n).continuous).trans
        (perfectOpenScalarFineCubeTerminalWord j r q hq n p)).Homotopy
      ((perfectOpenScalarFineCubeInclusionPath j r q hq n p).trans
        ((perfectOpenScalarFineProjectionCubePath j r n p).map
          (perfectOpenScalarCubeChangeWeak j n).continuous)).symm  :=
  perfectOpenScalarCubeReturnHomotopy j r q hq n p

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
theorem original_perfectOpenScalarCubeReturnHomotopy_boundary (a t : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarCubeReturnHomotopy j r q hq n p (a, t) z = (W).kBasepoint  :=
  perfectOpenScalarCubeReturnHomotopy_boundary j r q hq n p a t z hz

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
def original_perfectOpenScalarCubeCompositionPath : Path b b  :=
  perfectOpenScalarCubeCompositionPath j r q hq n p

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
theorem original_perfectOpenScalarCubeReturn_inverseCompositionClass :
    genLoopSelfTrackClass n b
        (((perfectOpenScalarFineCubeReturn j r n p).map
          (perfectOpenScalarCubeChangeWeak j n).continuous).trans
            (perfectOpenScalarFineCubeTerminalWord j r q hq n p)) =
      (genLoopSelfTrackClass n b
        (perfectOpenScalarCubeCompositionPath j r q hq n p))⁻¹  :=
  perfectOpenScalarCubeReturn_inverseCompositionClass j r q hq n p

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
def original_perfectOpenScalarFiberReturnLoop : Path (F af) (F af)  :=
  perfectOpenScalarFiberReturnLoop j r q hq n p

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
def original_perfectOpenScalarFiberNormalizedCube :
    GenLoop (Fin (n + 2)) (W).Delooping (W).kBasepoint  :=
  perfectOpenScalarFiberNormalizedCube j r q hq n p

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
theorem original_perfectOpenScalarNormalizedTerminalNull_prefix :
    perfectOpenScalarNormalizedTerminalNull j r q hq n p =
      HomotopyFiber.genLoopPrefixNull f (W).kBasepoint (V).kBasepoint h n lambda  :=
  perfectOpenScalarNormalizedTerminalNull_prefix j r q hq n p

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
def original_perfectOpenScalarNormalizedReturnHomotopy :
    (loopCurry (perfectOpenScalarFiberNormalizedCube j r q hq n p)).val.HomotopyRel
      (genLoopOfBasedPath
        (HomotopyFiber.genLoopReturnedLoop f (W).kBasepoint (V).kBasepoint h n
          (GenLoopPrefix.inversePrefix n af df)
          (perfectOpenScalarNormalizedTerminalNull j r q hq n p)
          (HomotopyFiber.genLoopPrefixReturn n R))).val
      (Cube.boundary (Fin (n + 1)))  :=
  perfectOpenScalarNormalizedReturnHomotopy j r q hq n p

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
def original_perfectOpenScalarNormalizedFiberHomotopy :
    (GenLoop.postcomp iota hiota
      (loopCurry (perfectOpenScalarFiberNormalizedCube j r q hq n p))).val.HomotopyRel
      (GenLoop.postcomp (canonicalFiberMap N) (canonicalFiberMap_basepoint N)
        (perfectOpenScalarCanonicalAcyclicCube j r q hq n p)).val
      (Cube.boundary (Fin (n + 1)))  :=
  perfectOpenScalarNormalizedFiberHomotopy j r q hq n p

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
theorem original_perfectOpenScalarNormalizedFiberHomotopy_zero (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarNormalizedFiberHomotopy j r q hq n p (0, z) =
      iota (loopCurry (perfectOpenScalarFiberNormalizedCube j r q hq n p) z)  :=
  perfectOpenScalarNormalizedFiberHomotopy_zero j r q hq n p z

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
theorem original_perfectOpenScalarNormalizedFiberHomotopy_one (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarNormalizedFiberHomotopy j r q hq n p (1, z) =
      canonicalFiberMap N (perfectOpenScalarCanonicalAcyclicCube j r q hq n p z)  :=
  perfectOpenScalarNormalizedFiberHomotopy_one j r q hq n p z

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
theorem original_perfectOpenScalarNormalizedFiberHomotopy_boundary (s : unitInterval)
    (z : Fin (n + 1) → unitInterval) (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarNormalizedFiberHomotopy j r q hq n p (s, z) =
      HomotopyFiber.basepoint f (W).kBasepoint (V).kBasepoint h  :=
  perfectOpenScalarNormalizedFiberHomotopy_boundary j r q hq n p s z hz

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
theorem original_perfectOpenScalarNormalizedFiberHomotopy_zero_path
    (z : Fin (n + 1) → unitInterval) (t : unitInterval) :
    (perfectOpenScalarNormalizedFiberHomotopy j r q hq n p (0, z)).val.2 t =
      genLoopNormalizedSelfTrackPath n (F af)
        (perfectOpenScalarFiberReturnLoop j r q hq n p) t z  :=
  perfectOpenScalarNormalizedFiberHomotopy_zero_path j r q hq n p z t

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
theorem original_perfectOpenScalarNormalizedFiberHomotopy_one_path
    (z : Fin (n + 1) → unitInterval) (t : unitInterval) :
    (perfectOpenScalarNormalizedFiberHomotopy j r q hq n p (1, z)).val.2 t =
      acyclicNullhomotopy N (t, perfectOpenScalarCanonicalAcyclicCube j r q hq n p z)  :=
  perfectOpenScalarNormalizedFiberHomotopy_one_path j r q hq n p z t

/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
theorem original_perfectOpenScalarNormalizedCube_connecting :
    HomotopyFiber.connectingHom f (W).kBasepoint (V).kBasepoint h n
        (genLoopSelfTrackClass n (F af) (perfectOpenScalarFiberReturnLoop j r q hq n p)) =
      canonicalFiberKMap N n
        (KMap (perfectOpenScalarConeFunctor_waldhausenExact j r q hq) n
          (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n))  :=
  perfectOpenScalarNormalizedCube_connecting j r q hq n p

end Scalar

section DegreeZero
local instance (X : Scheme.{u}) : HasBinaryCoproducts (ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :=
  Additivity.hasBinaryCoproducts (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
  (p : GenLoop (Fin 1)
    |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙
      bisimplicialSSet (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|
    (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)))
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "N" => perfectOpenNested j
local notation "W" => NestedWeakEquivalences.coarse N
local notation "f" => changeWeakMap N
local notation "h" => changeWeakMap_basepoint N
local notation "F" => perfectOpenScalarCubeChangeWeak j 0
local notation "af" => scalarFineAdditivitySourceCube X
  (𝟙 (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
  (QuotientRows.oneIdToZero V) (perfectScalarIdentityFineCofibrationSequence (X := X)) 0 p
/-- Check the entire displayed signature, including all coordinates and hypotheses. -/
theorem degreeZero_perfectOpenScalarNormalizedCube_connecting :
    HomotopyFiber.connectingHom f (W).kBasepoint (V).kBasepoint h 0
        (genLoopSelfTrackClass 0 (F af) (perfectOpenScalarFiberReturnLoop j r q hq 0 p)) =
      canonicalFiberKMap N 0
        (KMap (perfectOpenScalarConeFunctor_waldhausenExact j r q hq) 0
          (⟦perfectScalarProjectionInputCube 0 p⟧ : (V).K 0))  :=
  perfectOpenScalarNormalizedCube_connecting j r q hq 0 p

end DegreeZero
end ColibTest.ScalarReturnComparison
