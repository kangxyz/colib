/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberOperationConnecting


/-! Whole original scalar fiber comparison and positive connecting-map clients, including K₀. -/
@[expose] public section
open Topology SSet
open Topology SSet CategoryTheory.Functor
noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry
open Topology AlgebraicGeometry.Scheme.Modules CategoryTheory.Waldhausen
    CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.Additivity
open scoped Topology Simplicial
universe u
namespace ColibTest.ScalarTrack.ScalarCofiberFiberComparison
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
  (n : ℕ) (p : GenLoop (Fin (n + 1))
    |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|
    (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)))
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "N" => perfectOpenNested j
local notation "W" => NestedWeakEquivalences.coarse N
local notation "f" => changeWeakMap N
local notation "h" => changeWeakMap_basepoint N
local notation "iota" => HomotopyFiber.loopInclusion f
  (Structure.kBasepoint W) (Structure.kBasepoint V) h
local notation "hiota" => HomotopyFiber.loopInclusion_refl f
  (Structure.kBasepoint W) (Structure.kBasepoint V) h

/-- The whole fiber homotopy has only the original geometric inputs. -/
def originalWholeFiberHomotopy :
    (GenLoop.postcomp iota hiota
      (loopCurry (perfectOpenScalarFiberNormalizedCube j r q hq n p))).val.HomotopyRel
      (GenLoop.postcomp (canonicalFiberMap N) (canonicalFiberMap_basepoint N)
        (perfectOpenScalarCanonicalAcyclicCube j r q hq n p)).val
      (Cube.boundary (Fin (n + 1))) :=
  perfectOpenScalarNormalizedFiberHomotopy j r q hq n p

/-- The original normalized return keeps the forward source cast and entire terminal null. -/
theorem original_terminal_null :
    perfectOpenScalarNormalizedTerminalNull j r q hq n p =
      HomotopyFiber.genLoopPrefixNull f (W).kBasepoint (V).kBasepoint h n
        (perfectOpenScalarFineCubeTerminalWord j r q hq n p) :=
  perfectOpenScalarNormalizedTerminalNull_prefix j r q hq n p

/-- Every initial spatial point is the exact coordinate-zero loop inclusion. -/
theorem original_initial_cube (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarNormalizedFiberHomotopy j r q hq n p (0, z) =
      iota (loopCurry (perfectOpenScalarFiberNormalizedCube j r q hq n p) z) :=
  perfectOpenScalarNormalizedFiberHomotopy_zero j r q hq n p z

/-- Every final spatial point is the original canonical map on the public acyclic cone. -/
theorem original_final_cube (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarNormalizedFiberHomotopy j r q hq n p (1, z) =
      canonicalFiberMap N (perfectOpenScalarCanonicalAcyclicCube j r q hq n p z) :=
  perfectOpenScalarNormalizedFiberHomotopy_one j r q hq n p z

/-- The full spatial boundary is fixed for every independent interpolation time. -/
theorem original_boundary (s : unitInterval) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    perfectOpenScalarNormalizedFiberHomotopy j r q hq n p (s, z) =
      HomotopyFiber.basepoint f (W).kBasepoint (V).kBasepoint h :=
  perfectOpenScalarNormalizedFiberHomotopy_boundary j r q hq n p s z hz

/-- The old null path retains every independent stored path time at the final face. -/
theorem original_final_null (z : Fin (n + 1) → unitInterval) (t : unitInterval) :
    (perfectOpenScalarNormalizedFiberHomotopy j r q hq n p (1, z)).val.2 t =
      acyclicNullhomotopy N (t, perfectOpenScalarCanonicalAcyclicCube j r q hq n p z) :=
  perfectOpenScalarNormalizedFiberHomotopy_one_path j r q hq n p z t

/-- Coordinate zero stays the track coordinate with all residual spatial coordinates unchanged. -/
theorem original_initial_null (z : Fin (n + 1) → unitInterval) (t : unitInterval) :
    (perfectOpenScalarNormalizedFiberHomotopy j r q hq n p (0, z)).val.2 t =
      perfectOpenScalarFiberNormalizedCube j r q hq n p (Fin.cons t z) := by
  rw [perfectOpenScalarNormalizedFiberHomotopy_zero_path]
  rfl

/-- The normalized original operation has positive cone sign under the actual connecting map. -/
theorem original_normalized_connecting :
    HomotopyFiber.connectingHom f (W).kBasepoint (V).kBasepoint h n
        (originalKSelfTrackOperation V W (perfectOpenScalarPrespectrumHomotopy j r q hq) n
          (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n)) =
      canonicalFiberKMap N n
        (KMap (perfectOpenScalarConeFunctor_waldhausenExact j r q hq) n
          (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n)) :=
  perfectOpenScalarKOperation_connecting_cube j r q hq n p

/-- The raw original operation uses the same original rebase and has the same positive sign. -/
theorem original_raw_connecting :
    HomotopyFiber.connectingHom f (W).kBasepoint (V).kBasepoint h n
        (originalKSelfTrackOperation V W (perfectOpenScalarOriginalHomotopy j r q hq) n
          (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n)) =
      canonicalFiberKMap N n
        (KMap (perfectOpenScalarConeFunctor_waldhausenExact j r q hq) n
          (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n)) :=
  perfectOpenScalarOriginalKOperation_connecting_cube j r q hq n p

variable (p0 : GenLoop (Fin 1)
  |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|
  (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)))

/-- K₀ input retains the actual full fiber homotopy without a degree-one additivity premise. -/
def originalKzeroFiberHomotopy :
    (GenLoop.postcomp iota hiota
      (loopCurry (perfectOpenScalarFiberNormalizedCube j r q hq 0 p0))).val.HomotopyRel
      (GenLoop.postcomp (canonicalFiberMap N) (canonicalFiberMap_basepoint N)
        (perfectOpenScalarCanonicalAcyclicCube j r q hq 0 p0)).val
      (Cube.boundary (Fin 1)) :=
  perfectOpenScalarNormalizedFiberHomotopy j r q hq 0 p0

/-- K₀ input keeps the entire spatial boundary throughout the comparison. -/
theorem original_kzero_boundary (s : unitInterval) (z : Fin 1 → unitInterval)
    (hz : z ∈ Cube.boundary (Fin 1)) :
    perfectOpenScalarNormalizedFiberHomotopy j r q hq 0 p0 (s, z) =
      HomotopyFiber.basepoint f (W).kBasepoint (V).kBasepoint h :=
  perfectOpenScalarNormalizedFiberHomotopy_boundary j r q hq 0 p0 s z hz

/-- The original K₀ scalar operation has the same positive canonical cone image. -/
theorem original_kzero_connecting :
    HomotopyFiber.connectingHom f (W).kBasepoint (V).kBasepoint h 0
        (originalKSelfTrackOperation V W (perfectOpenScalarPrespectrumHomotopy j r q hq) 0
          (⟦perfectScalarProjectionInputCube 0 p0⟧ : (V).K 0)) =
      canonicalFiberKMap N 0
        (KMap (perfectOpenScalarConeFunctor_waldhausenExact j r q hq) 0
          (⟦perfectScalarProjectionInputCube 0 p0⟧ : (V).K 0)) :=
  perfectOpenScalarKOperation_connecting_cube j r q hq 0 p0

end ColibTest.ScalarTrack.ScalarCofiberFiberComparison
