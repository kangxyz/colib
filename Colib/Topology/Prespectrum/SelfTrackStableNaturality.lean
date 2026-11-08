/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.SelfTrackHomotopyNaturality
public import Colib.Topology.Prespectrum.SelfTrackStableOperation

/-!
# Original-map naturality of the integer-graded self-track operation

The finite original-map equations pass through the same alternating signs,
exact degree/level reindexing, and original colimit legs.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/SelfTrackStableNaturality.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace Topology.LoopPrespectrum
variable {D E F G : LoopPrespectrum.{u}} {f : E ⟶ F}

/-- Target naturality at the actual unchanged stable stage. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackStableNaturality.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.stableStageOperation_postcomp (H : Homotopy f f) (j : F ⟶ G)
    (d : ℤ) (n : ℕ) :
    (H.postcomp j).stableStageOperation d n =
      H.stableStageOperation d n ≫ shiftedStableStageMap j d n := by
  apply AddCommGrpCat.ext
  intro a
  exact congrArg Additive.ofMul
    (H.homotopyClassOperation_postcomp j ((-d).toNat + n + 2) (d.toNat + n + 1)
      (Additive.toMul a))

/-- Source naturality at the actual unchanged stable stage. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackStableNaturality.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.stableStageOperation_precomp (H : Homotopy f f) (i : D ⟶ E)
    (d : ℤ) (n : ℕ) :
    (H.precomp i).stableStageOperation d n =
      (stableSystemMap i d).app n ≫ H.stableStageOperation d n := by
  apply AddCommGrpCat.ext
  intro a
  exact congrArg Additive.ofMul
    (H.homotopyClassOperation_precomp i ((-d).toNat + n + 2) (d.toNat + n + 1)
      (Additive.toMul a))

/-- The sign and exact integer reindexing retain target naturality. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackStableNaturality.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs", reassoc]
theorem Homotopy.correctedStableStageOperation_postcomp (H : Homotopy f f)
    (j : F ⟶ G) (d : ℤ) (n : ℕ) :
    ((-1 : ℤ) ^ n • (H.postcomp j).stableStageOperation d n) ≫
        (shiftedStableReindexIso G d n).hom =
      ((-1 : ℤ) ^ n • H.stableStageOperation d n) ≫
        (shiftedStableReindexIso F d n).hom ≫
          (stableSystemMap j (d + 1)).app (parameterStableOffset d + n) := by
  have h : (H.postcomp j).stableStageOperation d n ≫
      (shiftedStableReindexIso G d n).hom =
    H.stableStageOperation d n ≫ (shiftedStableReindexIso F d n).hom ≫
      (stableSystemMap j (d + 1)).app (parameterStableOffset d + n) := by
    rw [H.stableStageOperation_postcomp, Category.assoc, shiftedStableReindexIso_map]
  simpa only [Preadditive.zsmul_comp] using congrArg (fun h ↦ (-1 : ℤ) ^ n • h) h

/-- The sign and exact integer reindexing retain source naturality. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackStableNaturality.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs", reassoc]
theorem Homotopy.correctedStableStageOperation_precomp (H : Homotopy f f)
    (i : D ⟶ E) (d : ℤ) (n : ℕ) :
    ((-1 : ℤ) ^ n • (H.precomp i).stableStageOperation d n) ≫
        (shiftedStableReindexIso F d n).hom =
      (stableSystemMap i d).app n ≫
        ((-1 : ℤ) ^ n • H.stableStageOperation d n) ≫
          (shiftedStableReindexIso F d n).hom := by
  simp only [H.stableStageOperation_precomp, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, Category.assoc]

/-- The final integer-graded operation commutes with the supplied original target map. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackStableNaturality.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.stableOperation_postcomp (H : Homotopy f f) (j : F ⟶ G) (d : ℤ) :
    (H.postcomp j).stableOperation d =
      H.stableOperation d ≫ (stableHomotopyFunctor (d + 1)).map j := by
  apply colimit.hom_ext
  intro n
  change stableHomotopyι E d n ≫ (H.postcomp j).stableOperation d =
    stableHomotopyι E d n ≫ (H.stableOperation d ≫ (stableHomotopyFunctor (d + 1)).map j)
  rw [(H.postcomp j).stableOperation_ι, H.correctedStableStageOperation_postcomp_assoc,
    ← stableHomotopyι_naturality, ← H.stableOperation_ι_assoc]

/-- The final integer-graded operation commutes with the supplied original source map. -/
@[colib_ref "quillen"
    "Topology/Prespectrum/SelfTrackStableNaturality.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
theorem Homotopy.stableOperation_precomp (H : Homotopy f f) (i : D ⟶ E) (d : ℤ) :
    (H.precomp i).stableOperation d = (stableHomotopyFunctor d).map i ≫ H.stableOperation d := by
  apply colimit.hom_ext
  intro n
  change stableHomotopyι D d n ≫ (H.precomp i).stableOperation d =
    stableHomotopyι D d n ≫ ((stableHomotopyFunctor d).map i ≫ H.stableOperation d)
  rw [(H.precomp i).stableOperation_ι, H.correctedStableStageOperation_precomp_assoc,
    ← H.stableOperation_ι, ← Category.assoc, ← stableHomotopyι_naturality, Category.assoc]

end Topology.LoopPrespectrum
