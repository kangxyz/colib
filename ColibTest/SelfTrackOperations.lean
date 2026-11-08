/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.SelfTrackKOperation
public import Colib.KTheory.Waldhausen.Iterated.SelfTrackKOperationLevelOne
public import Colib.KTheory.Waldhausen.Iterated.SelfTrackKOperationIntertwining
public import Colib.KTheory.Waldhausen.Iterated.SelfTrackKOperationNaturality
public import Colib.KTheory.Waldhausen.Iterated.SelfTrackKOperationLevelExt
public import Colib.KTheory.Waldhausen.Iterated.SelfTrackKOperationPath
public import Colib.KTheory.Waldhausen.Iterated.ExactSelfTrackStableOperation
public import Colib.KTheory.Waldhausen.Iterated.ModelSelfTrackStableOperation
public import Colib.Topology.Prespectrum.SelfTrackStableInterchange
public import Colib.Topology.Prespectrum.SelfTrackStableConcatenation
public import Colib.Topology.Prespectrum.SelfTrackStableTimeOperations
public import Colib.Topology.Prespectrum.SelfTrackStableVanishing
public import Colib.Topology.Prespectrum.SelfTrackStableNullEvaluation

/-! # Complete original finite, stable and K-group self-track consumers

These checks retain the full original signatures, including K-zero, Pi-one,
independent track times, the original level-one inverse and signed stable stages.
Original consumer proofs are adapted from QuillenTest at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

section SelfTrackSuccessorPositiveConsumer
open Topology CategoryTheory.Waldhausen
/-! # The original degree-one successor representative and sign -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology Topology.LoopPrespectrum
universe u
namespace ColibTest.SelfTrackSuccessorPositive

/-- The first positive input retains independent original track and structure coordinates. -/
theorem original_degree_one_representative {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n : ℕ) (p : GenLoop (Fin 1) (E.space n) (E.point n)) :
    H.genLoopNormalizedSelfTrackCubeSecond (n + 1) 0
        (loopUncurry (GenLoop.postcomp (E.structureMap n) (E.map_point n) p)) =
      transposeGenLoop (0 : Fin 3) 1 Fin.zero_ne_one
        (loopUncurry (GenLoop.postcomp (F.structureMap n) (F.map_point n)
          (genLoopNormalizedSelfTrackCube 0 _ (H.genLoopPath n p)))) :=
  H.genLoopNormalizedSelfTrackCubeSecond_structure_positive n 0 p

/-- The successor sign includes input pi-one without assuming its operation is a homomorphism. -/
theorem original_degree_one_sign {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n : ℕ) (a : HomotopyGroup.Pi 1 (E.space n) (E.point n)) :
    H.homotopyClassOperation (n + 1) 1 (structurePiMap E n 0 a) =
      (structurePiMap F n 1 (H.homotopyClassOperation n 0 a))⁻¹ :=
  H.homotopyClassOperation_structure_sign_positive n 0 a

end ColibTest.SelfTrackSuccessorPositive

end SelfTrackSuccessorPositiveConsumer

section SelfTrackKOperationConsumer
open Topology CategoryTheory.Waldhausen
/-! # Unchanged original K-zero and higher-group self-track consumers -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
universe u v
namespace ColibTest.SelfTrackKOperation
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (W : CategoryTheory.Waldhausen.Structure C)
  (V : CategoryTheory.Waldhausen.Structure D)
variable {f : originalPrespectrum W ⟶ originalPrespectrum V}

/-- K-zero is included with the exact original stabilization, not an object-only map. -/
theorem original_kzero_stabilization (H : Homotopy f f) (a : W.K 0) :
    originalKStableEquiv V 1 (Additive.ofMul (originalKSelfTrackOperation W V H 0 a)) =
      H.stableOperation 0 (originalKStableEquiv W 0 (Additive.ofMul a)) :=
  originalKSelfTrackOperation_stable W V H 0 a

/-- The original group law is preserved in every nonnegative input degree. -/
theorem original_group_product (H : Homotopy f f) (n : ℕ) (a b : W.K n) :
    originalKSelfTrackOperation W V H n (a * b) =
      originalKSelfTrackOperation W V H n a * originalKSelfTrackOperation W V H n b :=
  (originalKSelfTrackOperation W V H n).map_mul a b

end ColibTest.SelfTrackKOperation

end SelfTrackKOperationConsumer

section GenLoopSelfTrackNullConsumer
open Topology CategoryTheory.Waldhausen
/-! # Exact supplied-null representative consumer -/
set_option warningAsError true
set_option autoImplicit false
open scoped Topology unitInterval
universe u
namespace ColibTest.GenLoopSelfTrackNull
open Topology
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Even at the first input degree, the exact supplied null and original track are retained. -/
theorem original_null_degree_one (p : GenLoop (Fin 1) X x) (α : Path p p)
    (Q : Path p GenLoop.const) :
    genLoopSelfTrackClass 0 p α =
      (⟦loopUncurry (genLoopOfBasedPath (Q.symm.trans (α.trans Q)))⟧ :
        HomotopyGroup.Pi 2 X x) :=
  genLoopSelfTrackClass_eq_null_conjugate 0 p α Q

/-- Uncurrying does not reorder the original null-conjugated track's coordinates. -/
theorem original_null_coordinates (m : ℕ) (p : GenLoop (Fin (m + 1)) X x)
    (α : Path p p) (Q : Path p GenLoop.const) (z : Fin (m + 2) → unitInterval) :
    loopUncurry (genLoopOfBasedPath (Q.symm.trans (α.trans Q))) z =
      (Q.symm.trans (α.trans Q)) (z 0) (Fin.tail z) := rfl

end ColibTest.GenLoopSelfTrackNull

end GenLoopSelfTrackNullConsumer

section SelfTrackKOperationPathConsumer
open Topology CategoryTheory.Waldhausen
/-! # Forward original K-zero path evaluation with the supplied representative retained -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
universe u v
namespace ColibTest.SelfTrackKOperationPath
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : CategoryTheory.Waldhausen.Structure C) (V : CategoryTheory.Waldhausen.Structure D)
  {f : originalPrespectrum W ⟶ originalPrespectrum V}

/-- The actual supplied path gives the forward normalization of the original level-one track. -/
theorem original_kzero_forward_path (H : Homotopy f f) (a : W.K 0)
    (γ : Path ((originalPrespectrum W).point 1) ((originalPrespectrum W).point 1))
    (hγ : W.asSmallKEquiv 0 a = ⟦(genLoopHomeomorphOfUnique (Fin 1)).symm γ⟧) :
    V.asSmallKEquiv 1 (originalKSelfTrackOperation W V H 0 a) =
      loopKOneNormalization (basedLoopMap (f.map 1) (f.map_point 1) γ)
        (FundamentalGroup.fromPath ⟦H.pathSelfTrack 1 γ⟧) :=
  originalKSelfTrackOperation_path W V H a γ hγ

end ColibTest.SelfTrackKOperationPath

end SelfTrackKOperationPathConsumer

section SelfTrackNullEvaluationConsumer
open Topology CategoryTheory.Waldhausen
/-! # Original null-loop representative and degree-one finite evaluation -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology Topology.LoopPrespectrum
universe u
namespace ColibTest.SelfTrackNullEvaluation

/-- The exact original map retains its original self-track and both original null paths. -/
theorem original_null_loop_cube {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (N : Homotopy f (zeroHom E F)) (n m : ℕ)
    (p : GenLoop (Fin (m + 1)) (E.space n) (E.point n)) :
    GenLoop.postcomp ((H.nullLoopMap N).map n) ((H.nullLoopMap N).map_point n) p =
      genLoopOfBasedPath ((N.genLoopPath n p).symm.trans
        ((H.genLoopPath n p).trans (N.genLoopPath n p))) :=
  H.nullLoopMap_genLoop_eq N n m p

/-- The original map evaluation already holds at input degree one. -/
theorem original_degree_one_evaluation {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (N : Homotopy f (zeroHom E F)) (n : ℕ)
    (a : HomotopyGroup.Pi 1 (E.space n) (E.point n)) :
    (loopShiftMulEquiv (x := F.point n) 0).symm
        (HomotopyGroup.piMap 0 ((H.nullLoopMap N).map n) ((H.nullLoopMap N).map_point n) a) =
      H.homotopyClassOperation n 0 a :=
  H.nullLoopMap_piMap N n 0 a

end ColibTest.SelfTrackNullEvaluation

end SelfTrackNullEvaluationConsumer

section SelfTrackSuccessorRepresentativeConsumer
open Topology CategoryTheory.Waldhausen
/-! Original successor structure and track time remain independent in the actual cubes. -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology Topology.LoopPrespectrum
universe u
namespace ColibTest.SelfTrackSuccessorRepresentative

/-- The original coherent family compares with the original uncurried structure cube pointwise. -/
theorem original_successor_normalized_cube {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n m : ℕ)
    (p : GenLoop (Fin (m + 2)) (E.space n) (E.point n)) :
    H.genLoopNormalizedSelfTrackCubeSecond (n + 1) (m + 1)
        (loopUncurry (GenLoop.postcomp (E.structureMap n) (E.map_point n) p)) =
      transposeGenLoop (0 : Fin (m + 4)) 1 Fin.zero_ne_one
        (loopUncurry (GenLoop.postcomp (F.structureMap n) (F.map_point n)
          (genLoopNormalizedSelfTrackCube (m + 1) _ (H.genLoopPath n p)))) :=
  H.genLoopNormalizedSelfTrackCubeSecond_structure n m p

end ColibTest.SelfTrackSuccessorRepresentative

end SelfTrackSuccessorRepresentativeConsumer

section SelfTrackStableNaturalityConsumer
open Topology CategoryTheory.Waldhausen
/-! # The original source and target maps on the integer-graded self-track operation -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology Topology.LoopPrespectrum
universe u
namespace ColibTest.SelfTrackStableNaturality

/-- The original target map is retained in every integer degree. -/
theorem original_target_map {E F G : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (j : F ⟶ G) (d : ℤ) :
    (H.postcomp j).stableOperation d =
      H.stableOperation d ≫ (stableHomotopyFunctor (d + 1)).map j :=
  H.stableOperation_postcomp j d

/-- The original source map is retained in every integer degree. -/
theorem original_source_map {D E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (i : D ⟶ E) (d : ℤ) :
    (H.precomp i).stableOperation d = (stableHomotopyFunctor d).map i ≫ H.stableOperation d :=
  H.stableOperation_precomp i d

end ColibTest.SelfTrackStableNaturality

end SelfTrackStableNaturalityConsumer

section SelfTrackKOperationIntertwiningConsumer
open Topology CategoryTheory.Waldhausen
/-! # The actual original K-zero map retains its full intertwining data -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology.LoopPrespectrum CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS
universe u v
namespace ColibTest.SelfTrackKOperationIntertwining
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (W : Structure C) (V : Structure D)
variable {f g : originalPrespectrum W ⟶ originalPrespectrum V}

/-- Equality of original K-zero homomorphisms uses the given track and full relative square. -/
theorem original_kzero_transport
    (H : Homotopy f f) (K : Homotopy g g) (T : Homotopy f g)
    (J : (H.trans T).RelHomotopy (T.trans K)) :
    originalKSelfTrackOperation W V H 0 = originalKSelfTrackOperation W V K 0 :=
  originalKSelfTrackOperation_intertwine W V H K T J 0

end ColibTest.SelfTrackKOperationIntertwining

end SelfTrackKOperationIntertwiningConsumer

section GenLoopSelfTrackConstConsumer
open Topology CategoryTheory.Waldhausen
/-! # Literal constant-cube self-track consumers -/
set_option warningAsError true
set_option autoImplicit false
open scoped Topology unitInterval
universe u
namespace ColibTest.GenLoopSelfTrackConst
open Topology
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- The least supported input degree still keeps the actual uncurried path class. -/
theorem original_degree_one
    (α : Path (GenLoop.const : GenLoop (Fin 1) X x) GenLoop.const) :
    genLoopSelfTrackClass 0 GenLoop.const α =
      (⟦loopUncurry (genLoopOfBasedPath α)⟧ : HomotopyGroup.Pi 2 X x) :=
  genLoopSelfTrackClass_const 0 α

/-- Track time is exactly the new first coordinate, with original coordinates in order. -/
theorem original_track_coordinates (m : ℕ)
    (α : Path (GenLoop.const : GenLoop (Fin (m + 1)) X x) GenLoop.const)
    (z : Fin (m + 2) → unitInterval) :
    loopUncurry (genLoopOfBasedPath α) z = α (z 0) (Fin.tail z) := rfl

end ColibTest.GenLoopSelfTrackConst

end GenLoopSelfTrackConstConsumer

section SelfTrackKOperationNaturalityConsumer
open Topology CategoryTheory.Waldhausen
/-! # Original exact-functor maps on K-zero and every higher self-track operation -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS
universe u v
namespace ColibTest.SelfTrackKOperationNaturality
variable {C D T : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} T]
  (W : Structure C) (V : Structure D) (U : Structure T)
  {f : originalPrespectrum W ⟶ originalPrespectrum V}

/-- Original K-zero target naturality retains the exact original K-one target map. -/
theorem original_kzero_target (H : Homotopy f f)
    {J : D ⥤ T} (hJ : IsExact V.cof V.weq U.cof U.weq J) :
    originalKSelfTrackOperation W U (H.postcomp (exactOriginalPrespectrumMap V U hJ)) 0 =
      (KMap hJ 1).comp (originalKSelfTrackOperation W V H 0) :=
  originalKSelfTrackOperation_postcomp W V U H hJ 0

/-- Original K-zero source naturality retains the exact original K-zero source map. -/
theorem original_kzero_source (H : Homotopy f f)
    {J : T ⥤ C} (hJ : IsExact U.cof U.weq W.cof W.weq J) :
    originalKSelfTrackOperation U V (H.precomp (exactOriginalPrespectrumMap U W hJ)) 0 =
      (originalKSelfTrackOperation W V H 0).comp (KMap hJ 0) :=
  originalKSelfTrackOperation_precomp W V U H hJ 0

/-- Every original higher target K-class follows the same unchanged exact functor. -/
theorem original_target_all_degrees (H : Homotopy f f)
    {J : D ⥤ T} (hJ : IsExact V.cof V.weq U.cof U.weq J) (n : ℕ) (a : W.K n) :
    originalKSelfTrackOperation W U (H.postcomp (exactOriginalPrespectrumMap V U hJ)) n a =
      KMap hJ (n + 1) (originalKSelfTrackOperation W V H n a) :=
  originalKSelfTrackOperation_postcomp_apply W V U H hJ n a

end ColibTest.SelfTrackKOperationNaturality

end SelfTrackKOperationNaturalityConsumer

section SelfTrackHomotopyClassConsumer
open Topology CategoryTheory.Waldhausen
/-! Original finite track classes retain representatives and their relative homotopies. -/
set_option warningAsError true
set_option autoImplicit false

open CategoryTheory
open Topology Topology.LoopPrespectrum
universe u
namespace ColibTest.SelfTrackHomotopyClass

/-- The quotient operation agrees on any two actual homotopic input cubes. -/
theorem original_homotopic_representatives {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n m : ℕ)
    {p q : GenLoop (Fin (m + 1)) (E.space n) (E.point n)} (h : GenLoop.Homotopic p q) :
    H.homotopyClassOperation n m ⟦p⟧ =
      genLoopSelfTrackClass m _ (H.genLoopPath n q) :=
  H.genLoopSelfTrackClass_congr n m h

/-- With the old one-higher vanishing hypothesis the entire quotient function is constant. -/
theorem original_vanishing_operation {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n m : ℕ)
    (hF : Subsingleton (HomotopyGroup.Pi (m + 2) (F.space n) (F.point n)))
    (a : HomotopyGroup.Pi (m + 1) (E.space n) (E.point n)) :
    H.homotopyClassOperation n m a = 1 := hF.elim _ _

end ColibTest.SelfTrackHomotopyClass

end SelfTrackHomotopyClassConsumer

section SelfTrackSuccessorSignConsumer
open Topology CategoryTheory.Waldhausen
/-! The finite successor equation retains the actual maps and the proved coordinate sign. -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology Topology.LoopPrespectrum
universe u
namespace ColibTest.SelfTrackSuccessorSign

/-- The one-higher original self-track class has the exact original successor sign. -/
theorem original_successor_sign {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n m : ℕ)
    (a : HomotopyGroup.Pi (m + 2) (E.space n) (E.point n)) :
    H.homotopyClassOperation (n + 1) (m + 2) (structurePiMap E n (m + 1) a) =
      (structurePiMap F n (m + 2) (H.homotopyClassOperation n (m + 1) a))⁻¹ :=
  H.homotopyClassOperation_structure_sign n m a

/-- The successor map still evaluates the original structure map before uncurrying. -/
theorem original_structure_representative (E : LoopPrespectrum.{u}) (n m : ℕ)
    (p : GenLoop (Fin (m + 2)) (E.space n) (E.point n)) :
    structurePiMap E n (m + 1) ⟦p⟧ =
      (⟦loopUncurry (GenLoop.postcomp (E.structureMap n) (E.map_point n) p)⟧ :
        HomotopyGroup.Pi (m + 3) (E.space (n + 1)) (E.point (n + 1))) :=
  structurePiMap_mk E n (m + 1) p

end ColibTest.SelfTrackSuccessorSign

end SelfTrackSuccessorSignConsumer

section SelfTrackIntertwiningConsumer
open Topology CategoryTheory.Waldhausen
/-! # Original operation transport uses an actual supplied comparison track -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology
universe u
namespace ColibTest.SelfTrackIntertwining
variable {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
variable (H : Homotopy f f) (K : Homotopy g g) (C : Homotopy f g)
variable (J : (H.trans C).RelHomotopy (C.trans K))
include J

/-- Different original maps are allowed; the given comparison is retained on Pi-one. -/
theorem pi_one_transport (n : ℕ)
    (a : HomotopyGroup.Pi 1 (E.space n) (E.point n)) :
    H.homotopyClassOperation n 0 a = K.homotopyClassOperation n 0 a :=
  H.homotopyClassOperation_intertwine K C J n 0 a

/-- The exact same comparison transports the original negative-one stable operation. -/
theorem negative_one_transport : H.stableOperation (-1) = K.stableOperation (-1) :=
  H.stableOperation_intertwine K C J (-1)

end ColibTest.SelfTrackIntertwining

end SelfTrackIntertwiningConsumer

section SelfTrackPathConsumer
open Topology CategoryTheory.Waldhausen
/-! # Literal original path coordinates and finite degree-one normalization consumers -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace ColibTest.SelfTrackPath
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- Track and spatial times remain the two original arguments, including spectrum level zero. -/
theorem original_level_zero_coordinates (H : Homotopy f f)
    (γ : Path (E.point 0) (E.point 0)) (t s : unitInterval) :
    H.pathSelfTrack 0 γ t s = H.level 0 (t, γ s) := rfl

/-- The actual cube track, with its corrected endpoint, has the same original path image. -/
theorem original_path_image (H : Homotopy f f) (n : ℕ)
    (γ : Path (E.point n) (E.point n)) :
    (H.genLoopPath n ((genLoopHomeomorphOfUnique (Fin 1)).symm γ)).map
        (genLoopHomeomorphOfUnique (Fin 1)).continuous = H.pathSelfTrack n γ :=
  H.genLoopPath_finOne_map n γ

/-- Finite degree one retains the exact original path normalization and its single inverse. -/
theorem original_degree_one_normalization (H : Homotopy f f) (n : ℕ)
    (γ : Path (E.point n) (E.point n)) :
    H.homotopyClassOperation n 0
        ⟦(genLoopHomeomorphOfUnique (Fin 1)).symm γ⟧ =
      (loopKOneNormalization (basedLoopMap (f.map n) (f.map_point n) γ)
        (FundamentalGroup.fromPath ⟦H.pathSelfTrack n γ⟧))⁻¹ :=
  H.homotopyClassOperation_finOne n γ

end ColibTest.SelfTrackPath

end SelfTrackPathConsumer

section SelfTrackHomotopyAdditivityConsumer
open Topology CategoryTheory.Waldhausen
/-! Actual finite self-track additivity in input degree at least two. -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology Topology.LoopPrespectrum
universe u
namespace ColibTest.SelfTrackHomotopyAdditivity

/-- The original quotient function respects spatial multiplication in input degree at least two. -/
theorem original_finite_track_product {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n m : ℕ)
    (a b : HomotopyGroup.Pi (m + 2) (E.space n) (E.point n)) :
    H.homotopyClassOperation n (m + 1) (a * b) =
      H.homotopyClassOperation n (m + 1) a * H.homotopyClassOperation n (m + 1) b :=
  H.homotopyClassOperation_mul n m a b

/-- The homomorphism still evaluates exactly the original cube and H-family. -/
theorem original_finite_track_hom_representative {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n m : ℕ)
    (p : GenLoop (Fin (m + 2)) (E.space n) (E.point n)) :
    H.homotopyClassOperationHom n m ⟦p⟧ =
      genLoopSelfTrackClass (m + 1) _ (H.genLoopPath n p) := rfl

end ColibTest.SelfTrackHomotopyAdditivity

end SelfTrackHomotopyAdditivityConsumer

section SelfTrackStableTimeOperationsConsumer
open Topology CategoryTheory.Waldhausen
/-! # Negative-degree consumers of literal stable track reversal -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology Topology.LoopPrespectrum
universe u
namespace ColibTest.SelfTrackStableTimeOperations
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- Reversal retains the actual negative-one stable group, without an Omega assumption. -/
theorem negative_one_reversal (H : Homotopy f f) :
    H.symm.stableOperation (-1) = -H.stableOperation (-1) :=
  H.stableOperation_symm (-1)

/-- The original degree-zero operation likewise retains its exact sign and tail. -/
theorem zero_reversal (H : Homotopy f f) :
    H.symm.stableOperation 0 = -H.stableOperation 0 :=
  H.stableOperation_symm 0

end ColibTest.SelfTrackStableTimeOperations

end SelfTrackStableTimeOperationsConsumer

section SelfTrackRelativeHomotopyConsumer
open Topology CategoryTheory.Waldhausen
/-! # Supplied relative tracks compare original finite and negative stable operations -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology
universe u
namespace ColibTest.SelfTrackRelativeHomotopy
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F} {H K : Homotopy f f}

/-- A supplied whole relative comparison already identifies the original Pi-one operation. -/
theorem pi_one_comparison (J : H.RelHomotopy K) (n : ℕ)
    (a : HomotopyGroup.Pi 1 (E.space n) (E.point n)) :
    H.homotopyClassOperation n 0 a = K.homotopyClassOperation n 0 a :=
  J.homotopyClassOperation_eq n 0 a

/-- The same actual relative comparison preserves the negative-one colimit operation. -/
theorem negative_one_comparison (J : H.RelHomotopy K) :
    H.stableOperation (-1) = K.stableOperation (-1) := J.stableOperation_eq (-1)

/-- A supplied contraction, not an assumed filler existence, kills the original stable operation. -/
theorem supplied_contraction_zero (J : H.RelHomotopy (Homotopy.refl f)) (d : ℤ) :
    H.stableOperation d = 0 :=
  (J.stableOperation_eq d).trans (Homotopy.stableOperation_refl d)

end ColibTest.SelfTrackRelativeHomotopy

end SelfTrackRelativeHomotopyConsumer

section SelfTrackStableOperationConsumer
open Topology CategoryTheory.Waldhausen
/-! Actual representatives and actual integer-graded colimit legs of the self-track operation. -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Topology Topology.LoopPrespectrum
universe u
namespace ColibTest.SelfTrackStableOperation

/-- The finite stage still evaluates the same original based cube and same original H-family. -/
theorem original_stage_representative {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (d : ℤ) (n : ℕ)
    (p : GenLoop (Fin (d.toNat + n + 2))
      (E.space ((-d).toNat + n + 2)) (E.point ((-d).toNat + n + 2))) :
    H.stableStageOperation d n (Additive.ofMul
      (⟦p⟧ : HomotopyGroup.Pi (d.toNat + n + 2)
        (E.space ((-d).toNat + n + 2)) (E.point ((-d).toNat + n + 2)))) =
      Additive.ofMul (genLoopSelfTrackClass (d.toNat + n + 1) _
        (H.genLoopPath ((-d).toNat + n + 2) p)) := rfl

/-- The final original stage leg includes its displayed sign and exact integer-degree tail. -/
theorem original_stable_stage_leg {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (d : ℤ) (n : ℕ) :
    stableHomotopyι E d n ≫ H.stableOperation d =
      ((-1 : ℤ) ^ n • H.stableStageOperation d n) ≫
        (shiftedStableReindexIso F d n).hom ≫
          stableHomotopyι F (d + 1) (parameterStableOffset d + n) :=
  H.stableOperation_ι d n

end ColibTest.SelfTrackStableOperation

end SelfTrackStableOperationConsumer

section SelfTrackStableConcatenationConsumer
open Topology CategoryTheory.Waldhausen
/-! # Original negative stable operations retain literal time composition -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology Topology.LoopPrespectrum
universe u
namespace ColibTest.SelfTrackStableConcatenation
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- No eventual stability assumption is needed for negative-degree time composition. -/
theorem negative_one_concatenation (H K : Homotopy f f) :
    (H.trans K).stableOperation (-1) = K.stableOperation (-1) + H.stableOperation (-1) :=
  H.stableOperation_trans K (-1)

/-- The literal constant track is zero even in negative degree. -/
theorem negative_one_constant : (Homotopy.refl f).stableOperation (-1) = 0 :=
  Homotopy.stableOperation_refl (-1)

end ColibTest.SelfTrackStableConcatenation

end SelfTrackStableConcatenationConsumer

section ExactSelfTrackStableOperationConsumer
open Topology CategoryTheory.Waldhausen
/-! # Original exact-functor inverse tracks on negative stable groups -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology.LoopPrespectrum CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS
universe u v
namespace ColibTest.ExactSelfTrackStableOperation
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (W : Structure C) (V : Structure D) {F : C ⥤ D}
variable (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- The inverse of the actual natural isomorphism negates the negative-one operation. -/
theorem negative_one_inverse (e : F ≅ F) :
    (exactOriginalPrespectrumIsoHomotopy W V hF hF e.symm).stableOperation (-1) =
      -(exactOriginalPrespectrumIsoHomotopy W V hF hF e).stableOperation (-1) :=
  exactIsoSelfTrack_stableOperation_symm W V hF e (-1)

/-- No replacement by a literal constant identity track is assumed. -/
theorem zero_identity :
    (exactOriginalPrespectrumIsoHomotopy W V hF hF (Iso.refl F)).stableOperation 0 = 0 :=
  exactIsoSelfTrack_stableOperation_refl W V hF 0

end ColibTest.ExactSelfTrackStableOperation

end ExactSelfTrackStableOperationConsumer

section SelfTrackHomotopyNaturalityConsumer
open Topology CategoryTheory.Waldhausen
/-! Original source and target maps are retained by the finite operation homomorphism. -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology Topology.LoopPrespectrum
universe u
namespace ColibTest.SelfTrackHomotopyNaturality

/-- Target naturality uses the actual supplied prespectrum map at the unchanged level. -/
theorem original_target_naturality {E F G : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (j : F ⟶ G) (n m : ℕ) :
    (H.postcomp j).homotopyClassOperationHom n m =
      (HomotopyGroup.piMap (m + 2) (j.map n) (j.map_point n)).comp
        (H.homotopyClassOperationHom n m) :=
  H.homotopyClassOperationHom_postcomp j n m

/-- Source naturality uses the actual supplied prespectrum map on the original sphere. -/
theorem original_source_naturality {D E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (i : D ⟶ E) (n m : ℕ) :
    (H.precomp i).homotopyClassOperationHom n m =
      (H.homotopyClassOperationHom n m).comp
        (HomotopyGroup.piMap (m + 1) (i.map n) (i.map_point n)) :=
  H.homotopyClassOperationHom_precomp i n m

end ColibTest.SelfTrackHomotopyNaturality

end SelfTrackHomotopyNaturalityConsumer

section GenLoopSelfTrackKOneConsumer
open Topology CategoryTheory.Waldhausen
/-! Original path coordinates and the genuine inversion between the two normalizations. -/
set_option warningAsError true
set_option autoImplicit false
open Topology
open scoped Topology unitInterval
universe u
namespace ColibTest.GenLoopSelfTrackKOne
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- The converted original self-track keeps both actual parameters. -/
theorem original_track_coordinates (γ : Path x x) (α : Path γ γ)
    (t s : unitInterval) :
    (α.map (genLoopHomeomorphOfUnique (Fin 1)).symm.continuous) t (fun _ => s) =
      α t s := rfl

/-- The two original classes cancel in the original second homotopy group. -/
theorem original_normalizations_cancel (γ : Path x x) (α : Path γ γ) :
    genLoopSelfTrackClass 0 ((genLoopHomeomorphOfUnique (Fin 1)).symm γ)
        (α.map (genLoopHomeomorphOfUnique (Fin 1)).symm.continuous) *
      loopKOneNormalization γ (FundamentalGroup.fromPath ⟦α⟧) = 1 := by
  rw [genLoopSelfTrackClass_finOne_eq_inv, inv_mul_cancel]

/-- The actual transposed normalized cube has the inverse original class. -/
theorem original_transposed_cube_class (γ : Path x x) (α : Path γ γ) :
    (⟦transposeGenLoop (0 : Fin 2) 1 Fin.zero_ne_one
      (loopUncurry ((genLoopHomeomorphOfUnique (Fin 1)).symm
        (loopNormalizedSelfTrack γ α)))⟧ : HomotopyGroup.Pi 2 X x) =
      (loopKOneNormalization γ (FundamentalGroup.fromPath ⟦α⟧))⁻¹ := by
  exact (transposeGenLoop_class (0 : Fin 2) 1 Fin.zero_ne_one _).trans
    (congrArg (fun a : HomotopyGroup.Pi 2 X x => a⁻¹)
      (loopNormalizedSelfTrack_finOne_cube_class γ α))

end ColibTest.GenLoopSelfTrackKOne

end GenLoopSelfTrackKOneConsumer

section SelfTrackStableVanishingConsumer
open Topology CategoryTheory.Waldhausen
/-! # Original stable vanishing without additional topological hypotheses -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology Topology.LoopPrespectrum
universe u
namespace ColibTest.SelfTrackStableVanishing

/-- Only the original intermediate one-higher stable group is required to vanish. -/
theorem original_null_map_all_degrees {E F G : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (j : F ⟶ G) (N : Homotopy (f ≫ j) (zeroHom E G))
    (d : ℤ) (hF : Subsingleton (stableHomotopyGroup F (d + 1))) :
    (stableHomotopyFunctor d).map ((H.postcomp j).nullLoopMap N) = 0 :=
  H.nullLoopMap_stableMap_zero_of_stable j N d hF

/-- Negative degree uses the same original cone transition and original stable degree zero. -/
theorem original_cone_negative_one {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (H : Homotopy f f) (hF : Subsingleton (stableHomotopyGroup F 0)) :
    (stableHomotopyFunctor (-1)).map (mappingConeLoopTransition f H) = 0 := by
  exact mappingConeLoopTransition_stableMap_zero_of_stable f H (-1) (by simpa using hF)

end ColibTest.SelfTrackStableVanishing

end SelfTrackStableVanishingConsumer

section SelfTrackKOperationLevelOneConsumer
open Topology CategoryTheory.Waldhausen
/-! # Original K-zero finite self-track sign consumer -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
universe u v
namespace ColibTest.SelfTrackKOperationLevelOne
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (W : CategoryTheory.Waldhausen.Structure C)
  (V : CategoryTheory.Waldhausen.Structure D)
variable {f : originalPrespectrum W ⟶ originalPrespectrum V}

/-- Original K-zero retains the exact small-model map and the level-one inverse sign. -/
theorem original_kzero_level_one (H : Homotopy f f) (a : W.K 0) :
    V.asSmallKEquiv 1 (originalKSelfTrackOperation W V H 0 a) =
      (H.homotopyClassOperation 1 0 (W.asSmallKEquiv 0 a))⁻¹ :=
  originalKSelfTrackOperation_levelOne W V H 0 a

end ColibTest.SelfTrackKOperationLevelOne

end SelfTrackKOperationLevelOneConsumer

section SelfTrackCoordinateChangeConsumer
open Topology CategoryTheory.Waldhausen
/-! The actual swapped-input, restored-output representative has the original higher class. -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology Topology.LoopPrespectrum
universe u
namespace ColibTest.SelfTrackCoordinateChange

/-- Changing the normalization coordinate preserves the class of the actual original H-track. -/
theorem original_second_normalization_class {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n m : ℕ)
    (p : GenLoop (Fin (m + 2)) (E.space n) (E.point n)) :
    (⟦H.genLoopNormalizedSelfTrackCubeSecond n m p⟧ :
      HomotopyGroup.Pi (m + 3) (F.space n) (F.point n)) =
        genLoopSelfTrackClass (m + 1) _ (H.genLoopPath n p) :=
  H.genLoopNormalizedSelfTrackCubeSecond_class n m p

/-- The same time slice of the same H-family retains the exact original coordinate swap. -/
theorem original_transposed_track_time {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n m : ℕ)
    (p : GenLoop (Fin (m + 2)) (E.space n) (E.point n)) (t : unitInterval) :
    H.genLoopPath n (transposeGenLoop 0 1 Fin.zero_ne_one p) t =
      transposeGenLoop 0 1 Fin.zero_ne_one (H.genLoopPath n p t) :=
  H.genLoopPath_transpose n (m + 2) 0 1 Fin.zero_ne_one p t

end ColibTest.SelfTrackCoordinateChange

end SelfTrackCoordinateChangeConsumer

section SelfTrackTimeOperationsConsumer
open Topology CategoryTheory.Waldhausen
/-! # Low-degree consumers of literal self-track time operations -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology
universe u
namespace ColibTest.SelfTrackTimeOperations
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- Reversal applies already to a supplied original Pi-one class. -/
theorem pi_one_reversal (H : Homotopy f f) (n : ℕ)
    (a : HomotopyGroup.Pi 1 (E.space n) (E.point n)) :
    H.symm.homotopyClassOperation n 0 a = (H.homotopyClassOperation n 0 a)⁻¹ :=
  H.homotopyClassOperation_symm n 0 a

/-- Original concatenation retains its interval halves and product order. -/
theorem pi_one_concatenation (H K : Homotopy f f) (n : ℕ)
    (a : HomotopyGroup.Pi 1 (E.space n) (E.point n)) :
    (H.trans K).homotopyClassOperation n 0 a =
      K.homotopyClassOperation n 0 a * H.homotopyClassOperation n 0 a :=
  H.homotopyClassOperation_trans K n 0 a

end ColibTest.SelfTrackTimeOperations

end SelfTrackTimeOperationsConsumer

section SelfTrackNonnegativeStageConsumer
open Topology CategoryTheory.Waldhausen
/-! # Original degree-zero stable-stage evaluation -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology Topology.LoopPrespectrum
universe u
namespace ColibTest.SelfTrackNonnegativeStage
variable {E F : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- The nonnegative system's first stage is the genuine second spectrum space. -/
theorem original_degree_zero (H : Homotopy f f)
    (a : HomotopyGroup.Pi 2 (E.space 2) (E.point 2)) :
    H.stableOperation 0 (stableHomotopyι E 0 0
        (nonnegativeStableStageEquiv E 0 (Additive.ofMul a))) =
      stableHomotopyι F 1 0
        (nonnegativeStableStageEquiv F 1
          (Additive.ofMul (H.homotopyClassOperation 2 1 a))) :=
  H.stableOperation_nonnegative_stage 0 a

end ColibTest.SelfTrackNonnegativeStage

end SelfTrackNonnegativeStageConsumer

section SelfTrackStableNullEvaluationConsumer
open Topology CategoryTheory.Waldhausen
/-! # Original null-loop and original mapping-cone transition in every integer degree -/
set_option warningAsError true
set_option autoImplicit false
open CategoryTheory Topology Topology.LoopPrespectrum
universe u
namespace ColibTest.SelfTrackStableNullEvaluation

/-- The same supplied original nullhomotopy occurs in the actual map being evaluated. -/
theorem original_null_map {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (N : Homotopy f (zeroHom E F)) (d : ℤ) :
    (stableHomotopyFunctor d).map (H.nullLoopMap N) ≫ (parameterStableHomotopyIso F d).hom =
      H.stableOperation d :=
  H.nullLoopMap_stableHomotopy N d

/-- The existing original cone transition factors through its existing original inclusion. -/
theorem original_cone_transition {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (H : Homotopy f f) (d : ℤ) :
    (stableHomotopyFunctor d).map (mappingConeLoopTransition f H) ≫
        (parameterStableHomotopyIso (mappingCone f) d).hom =
      H.stableOperation d ≫ (stableHomotopyFunctor (d + 1)).map (mappingConeInclusion f) :=
  mappingConeLoopTransition_stableHomotopy f H d

end ColibTest.SelfTrackStableNullEvaluation

end SelfTrackStableNullEvaluationConsumer

section InterchangeConsumer
open CategoryTheory CategoryTheory.Limits Topology Topology.LoopPrespectrum
universe u
namespace ColibTest.SelfTrackInterchange
variable {E F G K : LoopPrespectrum.{u}}
  {f : E ⟶ F} {g : E ⟶ G} {f' : G ⟶ K} {g' : F ⟶ K}
  (H : Homotopy f f) (J : Homotopy g g)
  (H' : Homotopy f' f') (J' : Homotopy g' g')

/-- Both independent complete tracks retain the actual finite interchange inverse. -/
theorem finite_interchange
    (h : ∀ n s t x, H'.level n (s, J.level n (t, x)) =
      J'.level n (t, H.level n (s, x))) (n m : ℕ)
    (a : HomotopyGroup.Pi (m + 2) (E.space n) (E.point n)) :
    J'.homotopyClassOperation n (m + 2) (H.homotopyClassOperation n (m + 1) a) =
      (H'.homotopyClassOperation n (m + 2) (J.homotopyClassOperation n (m + 1) a))⁻¹ :=
  H.homotopyClassOperation_interchange_sign J H' J' h n m a

/-- Stable anti-commutation needs the Omega condition only on the actual source. -/
theorem stable_interchange
    (h : ∀ n s t x, H'.level n (s, J.level n (t, x)) =
      J'.level n (t, H.level n (s, x))) (hE : E.IsOmega) (n : ℕ)
    (a : stableHomotopyGroup E (n : ℤ)) :
    J'.stableOperation ((n + 1 : ℕ) : ℤ) (H.stableOperation (n : ℤ) a) =
      -(H'.stableOperation ((n + 1 : ℕ) : ℤ) (J.stableOperation (n : ℤ) a)) :=
  H.stableOperation_interchange_sign J H' J' h hE n a

end ColibTest.SelfTrackInterchange
end InterchangeConsumer

section CompleteLevelsConsumer
open CategoryTheory Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
universe u v
namespace ColibTest.SelfTrackCompleteLevels
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : CategoryTheory.Waldhausen.Structure C) (V : CategoryTheory.Waldhausen.Structure D)

/-- Different endpoint maps are identified from their full actual level tracks. -/
theorem original_complete_levels
    {f g : originalPrespectrum W ⟶ originalPrespectrum V}
    (H : Homotopy f f) (J : Homotopy g g) (h : ∀ n, H.level n = J.level n) (n : ℕ) :
    originalKSelfTrackOperation W V H n = originalKSelfTrackOperation W V J n :=
  originalKSelfTrackOperation_eq_of_levels W V H J h n

end ColibTest.SelfTrackCompleteLevels
end CompleteLevelsConsumer

section StrictZeroConsumer
open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory Topology.LoopPrespectrum
universe u
namespace ColibTest.SelfTrackStrictZero
variable {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)

/-- Native strict-zero composition retains its actual reversed sum. -/
theorem original_strict_composition
    (e e' : F.hom.toFunctor ≅ F.hom.toFunctor) (d : ℤ) :
    (prespectrumIsoHomotopy F (e ≪≫ e')).stableOperation d =
      (prespectrumIsoHomotopy F e').stableOperation d +
        (prespectrumIsoHomotopy F e).stableOperation d :=
  prespectrumIsoHomotopy_stableOperation_comp F e e' d

/-- The actual native identity transformation has zero operation in every integer degree. -/
theorem original_strict_identity (d : ℤ) :
    (prespectrumIsoHomotopy F (Iso.refl F.hom.toFunctor)).stableOperation d = 0 :=
  prespectrumIsoHomotopy_stableOperation_refl F d

/-- Inverting the complete strict-zero automorphism negates its actual stable operation. -/
theorem original_strict_inverse (e : F.hom.toFunctor ≅ F.hom.toFunctor) (d : ℤ) :
    (prespectrumIsoHomotopy F e.symm).stableOperation d =
      -(prespectrumIsoHomotopy F e).stableOperation d :=
  prespectrumIsoHomotopy_stableOperation_symm F e d

end ColibTest.SelfTrackStrictZero
end StrictZeroConsumer
