/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Iterated.RowTransformationSpectrum
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopyNaturality

/-! # Exact evaluation of the complete first-row spectrum cell

Postcomposition retains the original transformation time and the entire distinguished row.
The statement is a whole prespectrum-map equality at every time, including degree zero.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor
open scoped Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory
variable {V W T : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
  (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))

/-- Actual exact evaluation preserves the entire first-row cell at each original time. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowTransformationSpectrumNaturality.lean:26"
  "adaptation" "Original full first-row cell and exact evaluation at unchanged time."]
theorem rowTransformationSpectrumHomotopy_postcomp_at (J : W ⟶ T) (t : unitInterval) :
    (rowTransformationSpectrumHomotopy (F := F ≫ J) (G := G ≫ J)
      (whiskerRight η J.hom.toFunctor) (fun A => J.hom.isExact.weak _ (hη A))).at t =
    (rowTransformationSpectrumHomotopy η hη).at t ≫ rowLoopMap J := by
  change (prespectrumTransformationHomotopy (F := F ≫ J) (G := G ≫ J)
      (whiskerRight η J.hom.toFunctor) (fun A => J.hom.isExact.weak _ (hη A))).at t ≫
      rowStabilizationMap T =
    ((prespectrumTransformationHomotopy η hη).at t ≫ rowStabilizationMap W) ≫ rowLoopMap J
  rw [prespectrumTransformationHomotopy_postcomp_at, Category.assoc,
    rowStabilizationMap_naturality, Category.assoc]

end CategoryTheory.Waldhausen.IteratedS
