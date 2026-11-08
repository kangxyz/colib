/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberCubeReturnClass
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberInclusionDiagonal
public import Colib.KTheory.Waldhausen.Iterated.SelfTrackKOperationLevelOne
public import Colib.KTheory.Waldhausen.Iterated.SelfTrackKOperationIntertwining
public import Colib.Topology.Prespectrum.SelfTrackRelativeHomotopy
public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackNaturality

/-!
# The prescribed return is the actual scalar K-operation

The actual maps, whole tracks, signs and independent parameters are retained.
-/
/-! Implementation provenance:
    `Quillen/AlgebraicGeometry/PerfectComplexes/Spectrum/ScalarCofiberCubeReturnClass.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole tracks, signs and
    independent parameters are retained. -/
@[expose] public section
open Topology SSet CategoryTheory.Functor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
    CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open scoped Topology Simplicial
universe u v
private theorem scalarOperationEndpointCast {Y : Type v} [TopologicalSpace Y] {y : Y}
    (n : ℕ) {a b : GenLoop (Fin (n + 1)) Y y} (h : b = a) (P : Path a a) :
    genLoopSelfTrackClass n b (P.cast h h) = genLoopSelfTrackClass n a P := by
  subst b
  rfl

namespace AlgebraicGeometry.Scheme.Modules
local instance scalarOperationCoproducts (X : Scheme.{u}) : HasBinaryCoproducts
    (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :=
  Additivity.hasBinaryCoproducts (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
  (n : ℕ) (p : GenLoop (Fin (n + 1))
    |SSet.diagonalSSet (OrdinalSubdivision.δ.op ⋙ bisimplicialSSet
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace))|
    (subdivisionBasepoint (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)))
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "W" => NestedWeakEquivalences.coarse (perfectOpenNested j)
local notation "af" => scalarFineAdditivitySourceCube X (𝟙 (𝟭 (ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
  (QuotientRows.oneIdToZero V) (perfectScalarIdentityFineCofibrationSequence (X := X)) n p
local notation "b" => perfectOpenScalarCubeChangeWeak j n af
local notation "pSmall" => GenLoop.postcomp
  (ContinuousMap.HomotopyEquiv.toFun (Homeomorph.toHomotopyEquiv
    (Structure.asSmallDeloopingHomeomorph (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace))))
  (Structure.asSmallDeloopingHomeomorph_basepoint (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace))
  (perfectScalarProjectionInputCube n p)

/-- The entire cast inclusion edge is the original ordinary inclusion cylinder. -/
theorem perfectOpenScalarFineCubeInclusionPath_ordinary (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarFineCubeInclusionPath j r q hq n p t z =
      perfectOpenScalarInclusionRealizationHomotopy j r q hq
        (t, separatedFirstDeloopingMap V (p z)) := by
  change perfectOpenScalarCofiberCubeSquare j r q hq n p (t, 0) z = _
  rw [perfectOpenScalarCofiberCubeSquare_additivity_zero]
  exact perfectOpenScalarInclusionDiagonalRealization j r q hq t
    (realizedDiagonalMap (OrdinalSubdivision.horizontalEndpoint (bisimplicialSSet V)) (p z))

/-- Forward transport preserves every inclusion time and every original cube coordinate. -/
theorem perfectOpenScalarFineCubeInclusionPath_smallModel_apply (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    (perfectOpenScalarInclusionHomotopy j r q hq).genLoopPath 1 pSmall t z =
      (W).asSmallDeloopingHomeomorph
        (perfectOpenScalarFineCubeInclusionPath j r q hq n p t z) := by
  rw [perfectOpenScalarFineCubeInclusionPath_ordinary]
  exact perfectOpenScalarInclusionHomotopy_level_one j r q hq t
    (separatedFirstDeloopingMap V (p z))

/-- The same-rebase fine projection has its literal coarse image under forward transport. -/
theorem perfectOpenScalarFineProjectionCubePath_smallModel_apply (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    (perfectOpenScalarProjectionHomotopy j r).genLoopPath 1 pSmall t z =
      (W).asSmallDeloopingHomeomorph
        (perfectOpenScalarCubeChangeWeak j n
          (perfectOpenScalarFineProjectionCubePath j r n p t) z) := by
  rw [perfectOpenScalarFineProjectionCubePath_changeWeak]
  exact perfectOpenScalarProjectionHomotopy_level_one j r t
    (separatedFirstDeloopingMap V (p z))

/-- Forward transport keeps exactly the two original concatenation halves. -/
theorem perfectOpenScalarCubeCompositionPath_smallModel_apply (t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    ((perfectOpenScalarInclusionHomotopy j r q hq).trans
        (perfectOpenScalarProjectionHomotopy j r)).genLoopPath 1 pSmall t z =
      (W).asSmallDeloopingHomeomorph
        (perfectOpenScalarCubeCompositionPath j r q hq n p t z) := by
  rw [Homotopy.genLoopPath_trans]
  unfold perfectOpenScalarCubeCompositionPath
  simp only [Path.trans_apply]
  split_ifs
  · exact perfectOpenScalarFineCubeInclusionPath_smallModel_apply j r q hq n p _ z
  · exact perfectOpenScalarFineProjectionCubePath_smallModel_apply j r n p _ z

include r q hq in

/-- The source comparison is derived from time zero of the same entire composition loop. -/
theorem perfectOpenScalarCubeCompositionPath_smallModel_endpoint :
    GenLoop.postcomp (W).asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun
        (W).asSmallDeloopingHomeomorph_basepoint b =
      GenLoop.postcomp
        ((exactOriginalPrespectrumMap V W (changeWeak_exact (perfectOpenNested j))).map 1)
        ((exactOriginalPrespectrumMap V W (changeWeak_exact (perfectOpenNested j))).map_point 1)
        pSmall := by
  apply GenLoop.ext
  intro z
  have hs := congrArg (fun a => a z)
    (perfectOpenScalarCubeCompositionPath j r q hq n p).source
  have ht := perfectOpenScalarCubeCompositionPath_smallModel_apply j r q hq n p 0 z
  have hH := congrArg (fun a => a z)
    (((perfectOpenScalarInclusionHomotopy j r q hq).trans
      (perfectOpenScalarProjectionHomotopy j r)).genLoopPath 1 pSmall).source
  exact (congrArg (W).asSmallDeloopingHomeomorph hs).symm.trans (ht.symm.trans hH)

/-- The full mapped loop uses the symmetric source equality at both endpoints. -/
theorem perfectOpenScalarCubeCompositionPath_smallModel :
    ((perfectOpenScalarCubeCompositionPath j r q hq n p).map
      (genLoopPostcompContinuousMap (W).asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun
        (W).asSmallDeloopingHomeomorph_basepoint).continuous).cast
          (perfectOpenScalarCubeCompositionPath_smallModel_endpoint j r q hq n p).symm
          (perfectOpenScalarCubeCompositionPath_smallModel_endpoint j r q hq n p).symm =
      ((perfectOpenScalarInclusionHomotopy j r q hq).trans
        (perfectOpenScalarProjectionHomotopy j r)).genLoopPath 1 pSmall := by
  apply Path.ext
  funext t
  apply GenLoop.ext
  intro z
  exact (perfectOpenScalarCubeCompositionPath_smallModel_apply j r q hq n p t z).symm

/-- The existing original prespectrum triangle evaluates on the unchanged transported cube. -/
def perfectOpenScalarCompositionCubeHomotopy :
    ((perfectOpenScalarPrespectrumHomotopy j r q hq).genLoopPath 1 pSmall).Homotopy
      (((perfectOpenScalarInclusionHomotopy j r q hq).trans
        (perfectOpenScalarProjectionHomotopy j r)).genLoopPath 1 pSmall) :=
  (perfectOpenScalarProjectionCompositionTrack j r q hq).genLoopPathHomotopy 1 n pSmall

/-- The entire original triangle evaluation retains the exact old relative-homotopy data. -/
theorem perfectOpenScalarCompositionCubeHomotopy_eq :
    perfectOpenScalarCompositionCubeHomotopy j r q hq n p =
      (perfectOpenScalarProjectionCompositionTrack j r q hq).genLoopPathHomotopy 1 n pSmall :=
  rfl

/-- Evaluating the entire original homotopy keeps both independent times and spatial coordinates. -/
theorem perfectOpenScalarCompositionCubeHomotopy_data_apply (a t : unitInterval)
    (z : Fin (n + 1) → unitInterval) :
    perfectOpenScalarCompositionCubeHomotopy j r q hq n p (a, t) z =
      Homotopy.RelHomotopy.genLoopPathHomotopy
        (perfectOpenScalarProjectionCompositionTrack j r q hq) 1 n pSmall (a, t) z :=
  congrArg (fun Q => Q (a, t) z)
    (perfectOpenScalarCompositionCubeHomotopy_eq j r q hq n p)

/-- The original normalized scalar operation is the inverse class of the whole composition loop. -/
theorem perfectOpenScalarKOperation_compositionCube :
    originalKSelfTrackOperation V W (perfectOpenScalarPrespectrumHomotopy j r q hq) n
        (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n) =
      (genLoopSelfTrackClass n b (perfectOpenScalarCubeCompositionPath j r q hq n p))⁻¹ := by
  let H := perfectOpenScalarPrespectrumHomotopy j r q hq
  let T := (perfectOpenScalarInclusionHomotopy j r q hq).trans
    (perfectOpenScalarProjectionHomotopy j r)
  let L := (W).asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun
  let P := perfectOpenScalarCubeCompositionPath j r q hq n p
  have hc : genLoopSelfTrackClass n _ (T.genLoopPath 1 pSmall) =
      (W).asSmallKEquiv (n + 1) (genLoopSelfTrackClass n b P) := by
    rw [← perfectOpenScalarCubeCompositionPath_smallModel j r q hq n p,
      scalarOperationEndpointCast]
    exact (genLoopSelfTrackClass_naturality L
      (W).asSmallDeloopingHomeomorph_basepoint n b P).symm
  apply ((W).asSmallKEquiv (n + 1)).injective
  calc
    (W).asSmallKEquiv (n + 1)
        (originalKSelfTrackOperation V W H n ⟦perfectScalarProjectionInputCube n p⟧) =
        (H.homotopyClassOperation 1 n
          ((V).asSmallKEquiv n ⟦perfectScalarProjectionInputCube n p⟧))⁻¹ :=
      originalKSelfTrackOperation_levelOne V W H n ⟦perfectScalarProjectionInputCube n p⟧
    _ = (T.homotopyClassOperation 1 n
          ((V).asSmallKEquiv n ⟦perfectScalarProjectionInputCube n p⟧))⁻¹ :=
      congrArg Inv.inv (Homotopy.RelHomotopy.homotopyClassOperation_eq
        (perfectOpenScalarProjectionCompositionTrack j r q hq) 1 n _)
    _ = (genLoopSelfTrackClass n _ (T.genLoopPath 1 pSmall))⁻¹ := rfl
    _ = ((W).asSmallKEquiv (n + 1) (genLoopSelfTrackClass n b P))⁻¹ :=
      congrArg Inv.inv hc
    _ = (W).asSmallKEquiv (n + 1) (genLoopSelfTrackClass n b P)⁻¹ :=
      (map_inv ((W).asSmallKEquiv (n + 1)) _).symm

/-- The literal signed return represents the original normalized operation,
including degree zero. -/
theorem perfectOpenScalarCubeReturn_class :
    genLoopSelfTrackClass n b
        (((perfectOpenScalarFineCubeReturn j r n p).map
          (perfectOpenScalarCubeChangeWeak j n).continuous).trans
            (perfectOpenScalarFineCubeTerminalWord j r q hq n p)) =
      originalKSelfTrackOperation V W (perfectOpenScalarPrespectrumHomotopy j r q hq) n
        (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n) := by
  calc
    _ = genLoopSelfTrackClass n b
        (perfectOpenScalarCubeCompositionPath j r q hq n p).symm :=
      (genLoopSelfTrackClass_eq_iff n b _ _).mpr
        ⟨perfectOpenScalarCubeReturnHomotopy j r q hq n p⟩
    _ = (genLoopSelfTrackClass n b
        (perfectOpenScalarCubeCompositionPath j r q hq n p))⁻¹ :=
      genLoopSelfTrackClass_symm n b _
    _ = _ := (perfectOpenScalarKOperation_compositionCube j r q hq n p).symm

/-- The raw scalar corollary retains the actual normalization prefix and whole intertwining. -/
theorem perfectOpenScalarCubeReturn_originalClass :
    genLoopSelfTrackClass n b
        (((perfectOpenScalarFineCubeReturn j r n p).map
          (perfectOpenScalarCubeChangeWeak j n).continuous).trans
            (perfectOpenScalarFineCubeTerminalWord j r q hq n p)) =
      originalKSelfTrackOperation V W (perfectOpenScalarOriginalHomotopy j r q hq) n
        (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n) := by
  rw [perfectOpenScalarCubeReturn_class]
  exact congrArg (fun f => f (⟦perfectScalarProjectionInputCube n p⟧ : (V).K n))
    (originalKSelfTrackOperation_intertwine V W
      (perfectOpenScalarOriginalHomotopy j r q hq)
      (perfectOpenScalarPrespectrumHomotopy j r q hq)
      (perfectOpenChangeWeakNormalizationHomotopy j)
      (perfectOpenScalarNormalizationTrack j r q hq) n).symm

end AlgebraicGeometry.Scheme.Modules

-- COL-0324 references
attribute [colib_ref "quillen"
  "PerfectComplexes/Spectrum/ScalarCofiberCubeReturnClass.lean:1-257"
  "adaptation" "Actual whole tracks, canonical normalization and operation comparison"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFineCubeInclusionPath_ordinary
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFineCubeInclusionPath_smallModel_apply
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFineProjectionCubePath_smallModel_apply
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCubeCompositionPath_smallModel_apply
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCubeCompositionPath_smallModel_endpoint
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCubeCompositionPath_smallModel
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCompositionCubeHomotopy
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCompositionCubeHomotopy_eq
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCompositionCubeHomotopy_data_apply
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarKOperation_compositionCube
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCubeReturn_class
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCubeReturn_originalClass

attribute [colib_tag "COL-0324"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarFineCubeInclusionPath_ordinary
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCubeCompositionPath_smallModel
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarKOperation_compositionCube
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCubeReturn_class
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarCubeReturn_originalClass
