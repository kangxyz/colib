/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.ObjectNaturality
public import Colib.KTheory.Waldhausen.GrothendieckComparison.WeakObjectSquareTrack
public import Colib.KTheory.Waldhausen.BisimplexRealization
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.DegreeShift

/-! # Exact postcomposition of the entire original weak-arrow loop path

These intermediate comparisons retain the original strict chosen-zero hypothesis.
They compare actual paths with both independent coordinates and explicit endpoint casts.
-/
/-!
## Additional implementation provenance

Adapted from `Quillen/Waldhausen/AutomorphismKOne.lean`, lines 182–209,
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original declarations, full coordinates, hypotheses and universes are retained.
Only native namespaces, precise imports and line wrapping change. Source-only, UNCOMPILED.
-/
@[expose] public section
noncomputable section
open SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity unitInterval
open scoped Simplicial Topology
universe u v
open Topology
namespace CategoryTheory.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D} {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- The based realization carries the actual object loop to its original image object loop. -/
theorem objectLoopMapEq (h0 : F.obj V.zero = W.zero) (A : C) :
    basedLoopMap (deloopingMap hF).hom (deloopingMap_basepoint_of_zeroEq hF h0)
        (V.kZeroObjectLoop A) = W.kZeroObjectLoop (F.obj A) :=
  deloopingMap_kZeroObjectLoop hF h0 A

/-- The full original weak-arrow path retains both coordinates under exact postcomposition. -/
theorem weakObjectSquareLoopPath_postcompose (h0 : F.obj V.zero = W.zero)
    {A : C} (f : A ⟶ A) (hf : V.weq f) :
    ((V.weakObjectSquareLoopPath f hf).map
      (basedLoopMap (deloopingMap hF).hom
        (deloopingMap_basepoint_of_zeroEq hF h0)).continuous).cast
        (objectLoopMapEq hF h0 A).symm (objectLoopMapEq hF h0 A).symm =
      W.weakObjectSquareLoopPath (F.map f) (hF.weak f hf) := by
  apply Path.ext
  funext s
  apply Path.ext
  funext t
  change deloopingMap hF
      (bisimplexRealization V (V.weakObjectSimplex f hf).val
        ((isSimplex₂_diagonal_iff _ _ _).mpr (V.weakObjectSimplex f hf).property)
        (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s)) = _
  rw [bisimplexRealization_postcompose]
  exact DFunLike.congr_fun (bisimplexRealization_congr W _ _
    ((isSimplex₂_diagonal_iff _ _ _).mpr
      (W.weakObjectSimplex (F.map f) (hF.weak f hf)).property)
    (weakObjectSimplex_postcompose hF h0 f hf))
    (StdSimplex.homeomorphI.symm t, StdSimplex.homeomorphI.symm s)

end CategoryTheory.Waldhausen
