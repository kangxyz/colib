/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Waldhausen.Iterated.RowTransformationCylinder
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopy

/-! # The independently constructed first row with both original realization cylinders

The outer coordinate is the first-S row and the inner coordinate is the weak transformation.
The whole realized map agrees with the original structure map applied to that transformation.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor Opposite MonoidalCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory SSet Topology
variable {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
  (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))

/-- Realize the actual finite coefficient cell with its two original intervals. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowTransformationRealization.lean:29"
  "adaptation" "Original ordered row and transformation cylinders on native Waldhausen objects."]
def rowTransformationRealization (k : ℕ) :
    C(unitInterval × (unitInterval × stageSpace k V), stageSpace (k + 1) W) :=
  ⟨fun z => SSet.toTop.map (rowTransformationCylinder η hη k)
    ((SSet.realizationCylinderIso ((stages k).obj V ⊗ Δ[1])).inv
      ((SSet.realizationCylinderIso ((stages k).obj V)).inv
        (z.2.2, ULift.up z.2.1), ULift.up z.1)), by
    apply (SSet.toTop.map (rowTransformationCylinder η hη k)).hom.continuous.comp
    apply (SSet.realizationCylinderIso ((stages k).obj V ⊗ Δ[1])).inv.hom.continuous.comp
    apply Continuous.prodMk
    · exact (SSet.realizationCylinderIso ((stages k).obj V)).inv.hom.continuous.comp
        (continuous_snd.snd.prodMk (continuous_uliftUp.comp continuous_snd.fst))
    · exact continuous_uliftUp.comp continuous_fst⟩

/-- The whole independent first row is the unchanged structure of the original track. -/
@[colib_tag "COL-0530", colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowTransformationRealization.lean:37"
  "adaptation" "Original ordered row and transformation cylinders on native Waldhausen objects."]
theorem rowTransformationRealization_structure (k : ℕ) (s t : unitInterval)
    (x : stageSpace k V) :
    rowTransformationRealization η hη k (s, (t, x)) =
      (prespectrum W).structureMap (k + 1)
        ((prespectrumTransformationHomotopy η hη).level (k + 1) (t, x)) s := by
  let A := (stages k).obj V
  let H := stageTransformationCylinder k η hη
  let p := (SSet.realizationCylinderIso (A ⊗ Δ[1])).inv
    ((SSet.realizationCylinderIso A).inv (x, ULift.up t), ULift.up s)
  have h := ConcreteCategory.congr_hom (SSet.realizationCylinderIso_inv_naturality H)
    ((SSet.realizationCylinderIso A).inv (x, ULift.up t), ULift.up s)
  change SSet.toTop.map (H ▷ Δ[1]) p =
    (SSet.realizationCylinderIso _).inv
      (SSet.toTop.map H ((SSet.realizationCylinderIso A).inv (x, ULift.up t)),
        ULift.up s) at h
  change SSet.toTop.map (rowTransformationCylinder η hη k) p = _
  rw [rowTransformationCylinder_eq, Functor.map_comp]
  change SSet.toTop.map (stageCylinder k W) (SSet.toTop.map (H ▷ Δ[1]) p) = _
  rw [h]
  rfl

end CategoryTheory.Waldhausen.IteratedS
