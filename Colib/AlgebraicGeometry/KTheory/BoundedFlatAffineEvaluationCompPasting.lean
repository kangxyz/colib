/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationModelCoherence
public import Colib.KTheory.Waldhausen.Iterated.SmallModelTransformationIso
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumPastingHomotopy
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCompTracks
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationSourceTransport
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumNamedTransformationLevels
public import Colib.Topology.Prespectrum.HomotopyNamedLevels
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumNamedIteratedLevels
public import Colib.Topology.Prespectrum.HomotopyNamedCastLevels

/-!
# Native affine evaluation composition pasting

The four actual transformations retain their native model endpoints. Their proved
whole diamond equation gives a relative comparison of the direct and iterated model
tracks. Identifying these tracks with the coefficient routes is a separate step.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules
local notation "A" => boundedAboveFlatAffineSectionModelMap
local notation "E" => boundedAboveFlatAffineEvaluationModelMap
local notation "P" => boundedAboveFlatAffinePullbackModelMap

private theorem nativeTransformation_weq
    (V W : WideSubcategory preservesZero.{u}) (F G : V ⟶ W)
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) [IsIso η] (s : V.obj.Obj) :
    W.obj.waldhausen.weq (η.app s) :=
  W.obj.waldhausen.weq_iso (η.app s) (inferInstanceAs (IsIso (η.app s)))

/-- The actual eta transformation with explicit native endpoints. -/
private def affineEvaluationCompEta {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (A (f ≫ g) ≫ E T).hom.toFunctor ⟶ (E R ≫ P (f ≫ g)).hom.toFunctor :=
  (boundedAboveFlatAffineEvaluationModelIso (f ≫ g)).hom

/-- Weak membership for the actual eta transformation. -/
private theorem affineEvaluationCompEta_weq {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (s : (boundedAboveFlatAffineSectionModel R).obj.Obj) :
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)).obj.waldhausen.weq
      ((affineEvaluationCompEta f g).app s) := by
  have : IsIso (affineEvaluationCompEta f g) := by
    unfold affineEvaluationCompEta
    infer_instance
  exact nativeTransformation_weq (boundedAboveFlatAffineSectionModel R)
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
    (A (f ≫ g) ≫ E T) (E R ≫ P (f ≫ g)) (affineEvaluationCompEta f g) s

/-- The actual theta transformation with explicit native endpoints. -/
private def affineEvaluationCompTheta {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (E R ≫ P (f ≫ g)).hom.toFunctor ⟶ (E R ≫ (P f ≫ P g)).hom.toFunctor :=
  modelWhiskerLeft (E R) (boundedAboveFlatAffinePullbackModelCompIso f g).hom

/-- Weak membership for the actual theta transformation. -/
private theorem affineEvaluationCompTheta_weq {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (s : (boundedAboveFlatAffineSectionModel R).obj.Obj) :
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)).obj.waldhausen.weq
      ((affineEvaluationCompTheta f g).app s) := by
  have : IsIso (affineEvaluationCompTheta f g) := by
    unfold affineEvaluationCompTheta
    infer_instance
  exact nativeTransformation_weq (boundedAboveFlatAffineSectionModel R)
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
    (E R ≫ P (f ≫ g)) (E R ≫ (P f ≫ P g)) (affineEvaluationCompTheta f g) s

/-- The actual beta transformation with explicit native endpoints. -/
private def affineEvaluationCompBeta {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (A (f ≫ g) ≫ E T).hom.toFunctor ⟶ (A f ≫ (E S ≫ P g)).hom.toFunctor :=
  modelEqToHom (boundedAboveFlatAffineEvaluationModelCompSource f g) ≫
    modelWhiskerLeft (A f) (boundedAboveFlatAffineEvaluationModelIso g).hom

/-- Weak membership for the actual beta transformation. -/
private theorem affineEvaluationCompBeta_weq {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (s : (boundedAboveFlatAffineSectionModel R).obj.Obj) :
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)).obj.waldhausen.weq
      ((affineEvaluationCompBeta f g).app s) := by
  have : IsIso (affineEvaluationCompBeta f g) := by
    unfold affineEvaluationCompBeta
    infer_instance
  exact nativeTransformation_weq (boundedAboveFlatAffineSectionModel R)
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
    (A (f ≫ g) ≫ E T) (A f ≫ (E S ≫ P g)) (affineEvaluationCompBeta f g) s

/-- The actual gamma transformation with explicit native endpoints. -/
private def affineEvaluationCompGamma {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (A f ≫ (E S ≫ P g)).hom.toFunctor ⟶ (E R ≫ (P f ≫ P g)).hom.toFunctor :=
  modelWhiskerRightAssoc (A f) (E S) (E R) (P f) (P g)
    (boundedAboveFlatAffineEvaluationModelIso f).hom

/-- Weak membership for the actual gamma transformation. -/
private theorem affineEvaluationCompGamma_weq {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (s : (boundedAboveFlatAffineSectionModel R).obj.Obj) :
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)).obj.waldhausen.weq
      ((affineEvaluationCompGamma f g).app s) := by
  have : IsIso (affineEvaluationCompGamma f g) := by
    unfold affineEvaluationCompGamma
    infer_instance
  exact nativeTransformation_weq (boundedAboveFlatAffineSectionModel R)
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
    (A f ≫ (E S ≫ P g)) (E R ≫ (P f ≫ P g)) (affineEvaluationCompGamma f g) s

/-- The actual whole native diamond, with the existing source transport. -/
private theorem affineEvaluationCompDiamond {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    affineEvaluationCompEta f g ≫ affineEvaluationCompTheta f g =
      affineEvaluationCompBeta f g ≫ affineEvaluationCompGamma f g := by
  simpa only [affineEvaluationCompEta, affineEvaluationCompTheta, affineEvaluationCompBeta,
    affineEvaluationCompGamma, Category.assoc] using
    boundedAboveFlatAffineEvaluationModelIso_comp_hom f g

/-- The direct native transformation route before identifying coefficient-track formulas. -/
@[no_expose]
def boundedAboveFlatAffineEvaluationCompModelDirectHomotopy
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Topology.LoopPrespectrum.Homotopy (prespectrumMap (A (f ≫ g) ≫ E T))
      (prespectrumMap (E R ≫ (P f ≫ P g))) :=
  (prespectrumTransformationHomotopy (affineEvaluationCompEta f g)
    (affineEvaluationCompEta_weq f g)).trans
      (prespectrumTransformationHomotopy (affineEvaluationCompTheta f g)
        (affineEvaluationCompTheta_weq f g))

/-- The iterated native transformation route, including the actual source transport. -/
@[no_expose]
def boundedAboveFlatAffineEvaluationCompModelIteratedHomotopy
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Topology.LoopPrespectrum.Homotopy (prespectrumMap (A (f ≫ g) ≫ E T))
      (prespectrumMap (E R ≫ (P f ≫ P g))) :=
  (prespectrumTransformationHomotopy (affineEvaluationCompBeta f g)
    (affineEvaluationCompBeta_weq f g)).trans
      (prespectrumTransformationHomotopy (affineEvaluationCompGamma f g)
        (affineEvaluationCompGamma_weq f g))

/-- Paste the actual native diamond relative to endpoints and the entire point line. -/
@[no_expose]
def boundedAboveFlatAffineEvaluationCompModelRelHomotopy
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedAboveFlatAffineEvaluationCompModelDirectHomotopy f g).RelHomotopy
      (boundedAboveFlatAffineEvaluationCompModelIteratedHomotopy f g) :=
  prespectrumTransformationPastingHomotopy
    (V := boundedAboveFlatAffineSectionModel R)
    (W := asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
    (F := A (f ≫ g) ≫ E T) (G := E R ≫ P (f ≫ g))
    (G' := A f ≫ (E S ≫ P g)) (H := E R ≫ (P f ≫ P g))
    (affineEvaluationCompEta f g) (affineEvaluationCompTheta f g)
    (affineEvaluationCompBeta f g) (affineEvaluationCompGamma f g)
    (affineEvaluationCompEta_weq f g) (affineEvaluationCompTheta_weq f g)
    (affineEvaluationCompBeta_weq f g) (affineEvaluationCompGamma_weq f g)
    (affineEvaluationCompDiamond f g)

private theorem affineOriginalPrespectrum_obj
    {C : Type*} [Category C] (W : Structure C) :
    originalPrespectrum W = prespectrum (asSmallCategory W) := by
  rfl

/-- This equation compares only the two actual transformation names. -/
private theorem affineEvaluationCompEta_eq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    affineEvaluationCompEta f g =
      (boundedAboveFlatAffineEvaluationModelIso (f ≫ g)).hom := by
  rfl

/-- No realization or weak-equivalence witness occurs in this constructor equation. -/
private theorem affineEvaluationCompTheta_eq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    affineEvaluationCompTheta f g =
      modelWhiskerLeft (E R) (boundedAboveFlatAffinePullbackModelCompIso f g).hom := by
  rfl

/-- The actual eta constructor equation acts on whole levels, with any honest weak
witness for the original transformation. The witness is not an added assumption in
any final affine theorem: its canonical value is supplied immediately below. -/
private theorem affineEvaluationCompEta_constructor_level
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (hη : ∀ x,
      (asSmallCategory
        (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace)).obj.waldhausen.weq
          ((boundedAboveFlatAffineEvaluationModelIso (f ≫ g)).hom.app x)) (n : ℕ) :
    (prespectrumTransformationHomotopy
      (F := A (f ≫ g) ≫ E T) (G := E R ≫ P (f ≫ g))
      (boundedAboveFlatAffineEvaluationModelIso (f ≫ g)).hom hη).level n =
        (prespectrumTransformationHomotopy
          (F := A (f ≫ g) ≫ E T) (G := E R ≫ P (f ≫ g))
          (affineEvaluationCompEta f g) (affineEvaluationCompEta_weq f g)).level n := by
  exact prespectrumTransformationHomotopy_level_eq_of_eq
    (V := boundedAboveFlatAffineSectionModel R)
    (W := asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
    (F := A (f ≫ g) ≫ E T) (G := E R ≫ P (f ≫ g))
    (boundedAboveFlatAffineEvaluationModelIso (f ≫ g)).hom (affineEvaluationCompEta f g)
    hη (affineEvaluationCompEta_weq f g) (affineEvaluationCompEta_eq f g).symm n

/-- First direct boundary: the original coefficient level and the actual named eta.
The source-transport theorem is used as a theorem, not simplified or unfolded. -/
private theorem affineEvaluationCompEta_level_heq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    HEq ((boundedAboveFlatAffineEvaluationCoefficientHomotopy (f ≫ g)).level n)
      ((prespectrumTransformationHomotopy
        (F := A (f ≫ g) ≫ E T) (G := E R ≫ P (f ≫ g))
        (affineEvaluationCompEta f g) (affineEvaluationCompEta_weq f g)).level n) := by
  exact (boundedAboveFlatAffineEvaluationCoefficientHomotopy_level_heq (f ≫ g) n).trans
    (heq_of_eq (affineEvaluationCompEta_constructor_level f g
      (fun x => (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace).asSmall.weq_iso _
        (by
          change IsIso ((boundedAboveFlatAffineEvaluationModelIso (f ≫ g)).hom.app x)
          infer_instance)) n))

/-- Retained checked projection from the original total pullback composition track. -/
private theorem affinePullbackCompHomotopy_level_heq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    HEq ((boundedAboveFlatAffinePullbackCompHomotopy f g).level n)
      ((prespectrumTransformationHomotopy (boundedAboveFlatAffinePullbackModelCompIso f g).hom
        (nativeTransformation_weq
          (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
          (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
          (P (f ≫ g)) (P f ≫ P g)
          (boundedAboveFlatAffinePullbackModelCompIso f g).hom)).level n) := by
  unfold boundedAboveFlatAffinePullbackCompHomotopy
  exact heq_of_eq (Topology.LoopPrespectrum.Homotopy.cast_level _ _ _ n)

/-- The precomposition object-presentation boundary, before theta name matching. -/
private theorem affineEvaluationCompTheta_precomp_level_heq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    HEq
      ((Topology.LoopPrespectrum.Homotopy.precomp
        (boundedAboveFlatAffineEvaluationPrespectrumMap R)
        (boundedAboveFlatAffinePullbackCompHomotopy f g)).level n)
      ((Topology.LoopPrespectrum.Homotopy.precomp (prespectrumMap (E R))
        (prespectrumTransformationHomotopy
          (F := P (f ≫ g)) (G := P f ≫ P g)
          (boundedAboveFlatAffinePullbackModelCompIso f g).hom
          (nativeTransformation_weq
            (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
            (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
            (P (f ≫ g)) (P f ≫ P g)
            (boundedAboveFlatAffinePullbackModelCompIso f g).hom))).level n) := by
  exact Topology.LoopPrespectrum.Homotopy.precomp_level_congr_objects
    (boundedAboveFlatAffineSectionPrespectrumFunctor_obj R)
    (affineOriginalPrespectrum_obj (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (affineOriginalPrespectrum_obj (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
    (boundedAboveFlatAffineEvaluationPrespectrumMap R) (prespectrumMap (E R))
    (boundedAboveFlatAffineEvaluationPrespectrumMap_heq R)
    (boundedAboveFlatAffinePullbackCompHomotopy f g)
    (prespectrumTransformationHomotopy
      (F := P (f ≫ g)) (G := P f ≫ P g)
      (boundedAboveFlatAffinePullbackModelCompIso f g).hom
      (nativeTransformation_weq
        (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
        (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
        (P (f ≫ g)) (P f ≫ P g)
        (boundedAboveFlatAffinePullbackModelCompIso f g).hom)) n
    (affinePullbackCompHomotopy_level_heq f g n)

/-- The actual named theta matches native precomposition by the abstract certificate.
There is no concrete simp over theta, whiskering or geometric model definitions. -/
private theorem affineEvaluationCompTheta_constructor_level
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    (Topology.LoopPrespectrum.Homotopy.precomp (prespectrumMap (E R))
      (prespectrumTransformationHomotopy
        (F := P (f ≫ g)) (G := P f ≫ P g)
        (boundedAboveFlatAffinePullbackModelCompIso f g).hom
        (nativeTransformation_weq
          (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
          (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
          (P (f ≫ g)) (P f ≫ P g)
          (boundedAboveFlatAffinePullbackModelCompIso f g).hom))).level n =
      (prespectrumTransformationHomotopy
        (F := E R ≫ P (f ≫ g)) (G := E R ≫ (P f ≫ P g))
        (affineEvaluationCompTheta f g) (affineEvaluationCompTheta_weq f g)).level n := by
  exact prespectrumModelWhiskerLeftHomotopy_level_of_eq
    (U := boundedAboveFlatAffineSectionModel R)
    (V := asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (W := asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
    (E R) («P» := P (f ≫ g)) (Q := P f ≫ P g)
    (boundedAboveFlatAffinePullbackModelCompIso f g).hom
    (nativeTransformation_weq
      (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
      (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
      (P (f ≫ g)) (P f ≫ P g)
      (boundedAboveFlatAffinePullbackModelCompIso f g).hom)
    (affineEvaluationCompTheta f g) (affineEvaluationCompTheta_weq f g)
    (affineEvaluationCompTheta_eq f g) n

/-- Second direct boundary, glued without reducing either proved constituent. -/
private theorem affineEvaluationCompTheta_level_heq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    HEq
      ((Topology.LoopPrespectrum.Homotopy.precomp
        (boundedAboveFlatAffineEvaluationPrespectrumMap R)
        (boundedAboveFlatAffinePullbackCompHomotopy f g)).level n)
      ((prespectrumTransformationHomotopy
        (F := E R ≫ P (f ≫ g)) (G := E R ≫ (P f ≫ P g))
        (affineEvaluationCompTheta f g) (affineEvaluationCompTheta_weq f g)).level n) := by
  exact (affineEvaluationCompTheta_precomp_level_heq f g n).trans
    (heq_of_eq (affineEvaluationCompTheta_constructor_level f g n))

/-- The actual total coefficient route has this unchanged concatenation constructor. -/
private theorem affineEvaluationCompDirectHomotopy_eq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    boundedAboveFlatAffineEvaluationCompDirectHomotopy f g =
      (boundedAboveFlatAffineEvaluationCoefficientHomotopy (f ≫ g)).trans
        (Topology.LoopPrespectrum.Homotopy.precomp
          (boundedAboveFlatAffineEvaluationPrespectrumMap R)
          (boundedAboveFlatAffinePullbackCompHomotopy f g)) := by
  rfl

/-- The actual model track has its original two named transformations as constructor. -/
private theorem affineEvaluationCompModelDirectHomotopy_eq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    boundedAboveFlatAffineEvaluationCompModelDirectHomotopy f g =
      (prespectrumTransformationHomotopy
        (F := A (f ≫ g) ≫ E T) (G := E R ≫ P (f ≫ g))
        (affineEvaluationCompEta f g) (affineEvaluationCompEta_weq f g)).trans
          (prespectrumTransformationHomotopy
            (F := E R ≫ P (f ≫ g)) (G := E R ≫ (P f ≫ P g))
            (affineEvaluationCompTheta f g) (affineEvaluationCompTheta_weq f g)) := by
  rfl

/-- The total coefficient route and actual native direct route agree as complete level
maps. Constructor equations and both whole-level boundaries were proved separately. -/
theorem boundedAboveFlatAffineEvaluationCompDirectHomotopy_level_heq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    HEq ((boundedAboveFlatAffineEvaluationCompDirectHomotopy f g).level n)
      ((boundedAboveFlatAffineEvaluationCompModelDirectHomotopy f g).level n) := by
  exact Topology.LoopPrespectrum.Homotopy.trans_level_congr_objects_of_eq
    (boundedAboveFlatAffineSectionPrespectrumFunctor_obj R)
    (affineOriginalPrespectrum_obj (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
    (boundedAboveFlatAffineEvaluationCompDirectHomotopy f g)
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy (f ≫ g))
    (Topology.LoopPrespectrum.Homotopy.precomp
      (boundedAboveFlatAffineEvaluationPrespectrumMap R)
      (boundedAboveFlatAffinePullbackCompHomotopy f g))
    (boundedAboveFlatAffineEvaluationCompModelDirectHomotopy f g)
    (prespectrumTransformationHomotopy
      (F := A (f ≫ g) ≫ E T) (G := E R ≫ P (f ≫ g))
      (affineEvaluationCompEta f g) (affineEvaluationCompEta_weq f g))
    (prespectrumTransformationHomotopy
      (F := E R ≫ P (f ≫ g)) (G := E R ≫ (P f ≫ P g))
      (affineEvaluationCompTheta f g) (affineEvaluationCompTheta_weq f g))
    (affineEvaluationCompDirectHomotopy_eq f g)
    (affineEvaluationCompModelDirectHomotopy_eq f g) n
    (affineEvaluationCompEta_level_heq f g n) (affineEvaluationCompTheta_level_heq f g n)

/-- The actual strict section spectrum arrow is its native model arrow. -/
private theorem affineSectionPrespectrumMap_heq
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    HEq (boundedAboveFlatAffineSectionPrespectrumFunctor.map f)
      (prespectrumMap (A f)) := by
  unfold boundedAboveFlatAffineSectionPrespectrumFunctor
  rfl

/-- Canonical original coefficient levels with the existing native weak witness.
The generic equality certificate handles proof witnesses without unfolding geometry. -/
private theorem affineEvaluationCoefficientNative_level_heq
    {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ) :
    HEq ((boundedAboveFlatAffineEvaluationCoefficientHomotopy f).level n)
      ((prespectrumTransformationHomotopy
      (F := A f ≫ E S) (G := E R ≫ P f)
      (boundedAboveFlatAffineEvaluationModelIso f).hom
      (nativeTransformation_weq
        (boundedAboveFlatAffineSectionModel R)
        (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace))
        (A f ≫ E S) (E R ≫ P f) (boundedAboveFlatAffineEvaluationModelIso f).hom)).level n) := by
  exact (boundedAboveFlatAffineEvaluationCoefficientHomotopy_level_heq f n).trans
    (heq_of_eq (prespectrumTransformationHomotopy_level_eq_of_eq
      (V := boundedAboveFlatAffineSectionModel R)
      (W := asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace))
      (F := A f ≫ E S) (G := E R ≫ P f)
      (boundedAboveFlatAffineEvaluationModelIso f).hom
        (boundedAboveFlatAffineEvaluationModelIso f).hom
      (fun x => (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace).asSmall.weq_iso _
        (by
          change IsIso ((boundedAboveFlatAffineEvaluationModelIso f).hom.app x)
          infer_instance))
      (nativeTransformation_weq
        (boundedAboveFlatAffineSectionModel R)
        (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace))
        (A f ≫ E S) (E R ≫ P f) (boundedAboveFlatAffineEvaluationModelIso f).hom) rfl n))

/-- The actual beta retains the specified native source-row equality. -/
private theorem affineEvaluationCompBeta_eq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    affineEvaluationCompBeta f g =
      modelEqToHom (boundedAboveFlatAffineEvaluationModelCompSource f g) ≫
        modelWhiskerLeft (A f) (boundedAboveFlatAffineEvaluationModelIso g).hom := by
  rfl

/-- Only the source-transported native beta constructor boundary. -/
private theorem affineEvaluationCompBeta_constructor_level
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    (Topology.LoopPrespectrum.Homotopy.precomp (prespectrumMap (A f))
      (prespectrumTransformationHomotopy
      (F := A g ≫ E T) (G := E S ≫ P g)
      (boundedAboveFlatAffineEvaluationModelIso g).hom
      (nativeTransformation_weq
        (boundedAboveFlatAffineSectionModel S)
        (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
        (A g ≫ E T) (E S ≫ P g) (boundedAboveFlatAffineEvaluationModelIso g).hom))).level n =
      (prespectrumTransformationHomotopy
      (F := A (f ≫ g) ≫ E T) (G := A f ≫ (E S ≫ P g))
      (affineEvaluationCompBeta f g) (affineEvaluationCompBeta_weq f g)).level n := by
  exact prespectrumModelWhiskerLeftSourceHomotopy_level_of_eq
    (U := boundedAboveFlatAffineSectionModel R)
    (V := boundedAboveFlatAffineSectionModel S)
    (W := asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
    (A f) («P» := A g ≫ E T) (Q := E S ≫ P g) (F := A (f ≫ g) ≫ E T)
    (boundedAboveFlatAffineEvaluationModelCompSource f g)
    (boundedAboveFlatAffineEvaluationModelIso g).hom (nativeTransformation_weq
        (boundedAboveFlatAffineSectionModel S)
        (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
        (A g ≫ E T) (E S ≫ P g) (boundedAboveFlatAffineEvaluationModelIso g).hom)
    (affineEvaluationCompBeta f g) (affineEvaluationCompBeta_weq f g)
    (affineEvaluationCompBeta_eq f g) n

/-- Only beta's original-object precomposition boundary, before source-row transport. -/
private theorem affineEvaluationCompBeta_precomp_level_heq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    HEq ((Topology.LoopPrespectrum.Homotopy.precomp
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map f)
      (boundedAboveFlatAffineEvaluationCoefficientHomotopy g)).level n)
        ((Topology.LoopPrespectrum.Homotopy.precomp (prespectrumMap (A f))
      (prespectrumTransformationHomotopy
      (F := A g ≫ E T) (G := E S ≫ P g)
      (boundedAboveFlatAffineEvaluationModelIso g).hom
      (nativeTransformation_weq
        (boundedAboveFlatAffineSectionModel S)
        (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
        (A g ≫ E T) (E S ≫ P g) (boundedAboveFlatAffineEvaluationModelIso g).hom))).level n) := by
  exact Topology.LoopPrespectrum.Homotopy.precomp_level_congr_objects
    (boundedAboveFlatAffineSectionPrespectrumFunctor_obj R)
    (boundedAboveFlatAffineSectionPrespectrumFunctor_obj S)
    (affineOriginalPrespectrum_obj (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
    (boundedAboveFlatAffineSectionPrespectrumFunctor.map f) (prespectrumMap (A f))
    (affineSectionPrespectrumMap_heq f)
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy g)
    (prespectrumTransformationHomotopy
      (F := A g ≫ E T) (G := E S ≫ P g)
      (boundedAboveFlatAffineEvaluationModelIso g).hom
      (nativeTransformation_weq
        (boundedAboveFlatAffineSectionModel S)
        (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
        (A g ≫ E T) (E S ≫ P g) (boundedAboveFlatAffineEvaluationModelIso g).hom)) n
    (affineEvaluationCoefficientNative_level_heq g n)

/-- The first original iterated subtrack, including its exact inner association cast. -/
private theorem affineEvaluationCompBeta_level_heq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    HEq (((Topology.LoopPrespectrum.Homotopy.precomp
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map f)
      (boundedAboveFlatAffineEvaluationCoefficientHomotopy g)).cast rfl (Category.assoc _ _
        _).symm).level n) ((prespectrumTransformationHomotopy
      (F := A (f ≫ g) ≫ E T) (G := A f ≫ (E S ≫ P g))
      (affineEvaluationCompBeta f g) (affineEvaluationCompBeta_weq f g)).level n) := by
  exact (heq_of_eq (Topology.LoopPrespectrum.Homotopy.cast_level
    (Topology.LoopPrespectrum.Homotopy.precomp
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map f)
      (boundedAboveFlatAffineEvaluationCoefficientHomotopy g)) rfl (Category.assoc
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map f)
        (boundedAboveFlatAffineEvaluationPrespectrumMap S) (prespectrumMap (P g))).symm
        n)).trans
      ((affineEvaluationCompBeta_precomp_level_heq f g n).trans
        (heq_of_eq (affineEvaluationCompBeta_constructor_level f g n)))

/-- The actual gamma is the existing native association-aware right whisker. -/
private theorem affineEvaluationCompGamma_eq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    affineEvaluationCompGamma f g =
      modelWhiskerRightAssoc (A f) (E S) (E R) (P f) (P g)
        (boundedAboveFlatAffineEvaluationModelIso f).hom := by
  rfl

/-- Only the native gamma constructor boundary, with right-associated endpoints. -/
private theorem affineEvaluationCompGamma_constructor_level
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    ((prespectrumTransformationHomotopy
      (F := A f ≫ E S) (G := E R ≫ P f)
      (boundedAboveFlatAffineEvaluationModelIso f).hom
      (nativeTransformation_weq
        (boundedAboveFlatAffineSectionModel R)
        (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace))
        (A f ≫ E S) (E R ≫ P f) (boundedAboveFlatAffineEvaluationModelIso f).hom)).postcomp
          (prespectrumMap (P g))).level n =
      (prespectrumTransformationHomotopy
      (F := A f ≫ (E S ≫ P g)) (G := E R ≫ (P f ≫ P g))
      (affineEvaluationCompGamma f g) (affineEvaluationCompGamma_weq f g)).level n := by
  exact prespectrumModelWhiskerRightAssocHomotopy_level_of_eq
    (U := boundedAboveFlatAffineSectionModel R)
    (V := boundedAboveFlatAffineSectionModel S)
    (W := asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace))
    (X := asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace))
    (Y := asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
    (A f) (E S) (E R) (P f) (P g)
    (boundedAboveFlatAffineEvaluationModelIso f).hom (nativeTransformation_weq
        (boundedAboveFlatAffineSectionModel R)
        (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace))
        (A f ≫ E S) (E R ≫ P f) (boundedAboveFlatAffineEvaluationModelIso f).hom)
    (affineEvaluationCompGamma f g) (affineEvaluationCompGamma_weq f g)
    (affineEvaluationCompGamma_eq f g) n

/-- Only gamma's original-object postcomposition boundary, before name matching. -/
private theorem affineEvaluationCompGamma_postcomp_level_heq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    HEq (((boundedAboveFlatAffineEvaluationCoefficientHomotopy f).postcomp
      (prespectrumMap (P g))).level n) (((prespectrumTransformationHomotopy
      (F := A f ≫ E S) (G := E R ≫ P f)
      (boundedAboveFlatAffineEvaluationModelIso f).hom
      (nativeTransformation_weq
        (boundedAboveFlatAffineSectionModel R)
        (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace))
        (A f ≫ E S) (E R ≫ P f) (boundedAboveFlatAffineEvaluationModelIso f).hom)).postcomp
          (prespectrumMap (P g))).level n) := by
  exact Topology.LoopPrespectrum.Homotopy.postcomp_level_congr_objects
    (boundedAboveFlatAffineSectionPrespectrumFunctor_obj R)
    (affineOriginalPrespectrum_obj (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace))
    (affineOriginalPrespectrum_obj (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
    (boundedAboveFlatAffineEvaluationCoefficientHomotopy f)
    (prespectrumTransformationHomotopy
      (F := A f ≫ E S) (G := E R ≫ P f)
      (boundedAboveFlatAffineEvaluationModelIso f).hom
      (nativeTransformation_weq
        (boundedAboveFlatAffineSectionModel R)
        (asSmallCategory (boundedAboveFlatPerfectWaldhausen (Spec S).toRingedSpace))
        (A f ≫ E S) (E R ≫ P f) (boundedAboveFlatAffineEvaluationModelIso f).hom))
    (prespectrumMap (P g)) (prespectrumMap (P g)) (HEq.rfl) n
    (affineEvaluationCoefficientNative_level_heq f n)

/-- The second original iterated subtrack and the actual gamma agree on whole levels. -/
private theorem affineEvaluationCompGamma_level_heq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    HEq (((boundedAboveFlatAffineEvaluationCoefficientHomotopy f).postcomp
      (prespectrumMap (P g))).level n) ((prespectrumTransformationHomotopy
      (F := A f ≫ (E S ≫ P g)) (G := E R ≫ (P f ≫ P g))
      (affineEvaluationCompGamma f g) (affineEvaluationCompGamma_weq f g)).level n) := by
  exact (affineEvaluationCompGamma_postcomp_level_heq f g n).trans
    (heq_of_eq (affineEvaluationCompGamma_constructor_level f g n))

/-- The actual outer source cast reverses strict section composition, as in CompTracks. -/
private theorem affineEvaluationCompIteratedSource_eq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    boundedAboveFlatAffineSectionPrespectrumFunctor.map f ≫
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map g ≫
          boundedAboveFlatAffineEvaluationPrespectrumMap T) =
      boundedAboveFlatAffineSectionPrespectrumFunctor.map (f ≫ g) ≫
        boundedAboveFlatAffineEvaluationPrespectrumMap T := by
  rw [← Category.assoc, ← boundedAboveFlatAffineSectionPrespectrumFunctor_map_comp]

/-- The actual outer target cast is the original forward association equality. -/
private theorem affineEvaluationCompIteratedTarget_eq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedAboveFlatAffineEvaluationPrespectrumMap R ≫ prespectrumMap (P f)) ≫
        prespectrumMap (P g) =
      boundedAboveFlatAffineEvaluationPrespectrumMap R ≫
        (prespectrumMap (P f) ≫ prespectrumMap (P g)) := by
  exact Category.assoc _ _ _

/-- The unchanged actual iterated constructor, including inner and both outer casts. -/
private theorem affineEvaluationCompIteratedHomotopy_eq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    boundedAboveFlatAffineEvaluationCompIteratedHomotopy f g =
      (((Topology.LoopPrespectrum.Homotopy.precomp
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map f)
      (boundedAboveFlatAffineEvaluationCoefficientHomotopy g)).cast rfl (Category.assoc _ _
        _).symm).trans ((boundedAboveFlatAffineEvaluationCoefficientHomotopy f).postcomp
      (prespectrumMap (P g)))).cast
        (affineEvaluationCompIteratedSource_eq f g)
        (affineEvaluationCompIteratedTarget_eq f g) := by
  rfl

/-- The unchanged model iterated constructor has the original named beta and gamma. -/
private theorem affineEvaluationCompModelIteratedHomotopy_eq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    boundedAboveFlatAffineEvaluationCompModelIteratedHomotopy f g =
      (prespectrumTransformationHomotopy
      (F := A (f ≫ g) ≫ E T) (G := A f ≫ (E S ≫ P g))
      (affineEvaluationCompBeta f g) (affineEvaluationCompBeta_weq f g)).trans
        (prespectrumTransformationHomotopy
      (F := A f ≫ (E S ≫ P g)) (G := E R ≫ (P f ≫ P g))
      (affineEvaluationCompGamma f g) (affineEvaluationCompGamma_weq f g)) := by
  rfl

/-- The actual iterated coefficient track and actual native iterated track agree on
all complete continuous level maps, with both object presentations kept independent. -/
theorem boundedAboveFlatAffineEvaluationCompIteratedHomotopy_level_heq
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (n : ℕ) :
    HEq ((boundedAboveFlatAffineEvaluationCompIteratedHomotopy f g).level n)
      ((boundedAboveFlatAffineEvaluationCompModelIteratedHomotopy f g).level n) := by
  exact Topology.LoopPrespectrum.Homotopy.trans_cast_level_congr_objects_of_eq
    (boundedAboveFlatAffineSectionPrespectrumFunctor_obj R)
    (affineOriginalPrespectrum_obj (boundedAboveFlatPerfectWaldhausen (Spec T).toRingedSpace))
    (boundedAboveFlatAffineEvaluationCompIteratedHomotopy f g)
    ((Topology.LoopPrespectrum.Homotopy.precomp
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map f)
      (boundedAboveFlatAffineEvaluationCoefficientHomotopy g)).cast rfl (Category.assoc
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map f)
        (boundedAboveFlatAffineEvaluationPrespectrumMap S) (prespectrumMap (P g))).symm)
        ((boundedAboveFlatAffineEvaluationCoefficientHomotopy f).postcomp
      (prespectrumMap (P g)))
    (affineEvaluationCompIteratedSource_eq f g)
    (affineEvaluationCompIteratedTarget_eq f g)
    (boundedAboveFlatAffineEvaluationCompModelIteratedHomotopy f g)
    (prespectrumTransformationHomotopy
      (F := A (f ≫ g) ≫ E T) (G := A f ≫ (E S ≫ P g))
      (affineEvaluationCompBeta f g) (affineEvaluationCompBeta_weq f g))
        (prespectrumTransformationHomotopy
      (F := A f ≫ (E S ≫ P g)) (G := E R ≫ (P f ≫ P g))
      (affineEvaluationCompGamma f g) (affineEvaluationCompGamma_weq f g))
    (affineEvaluationCompIteratedHomotopy_eq f g)
    (affineEvaluationCompModelIteratedHomotopy_eq f g) n
    (affineEvaluationCompBeta_level_heq f g n) (affineEvaluationCompGamma_level_heq f g n)

end AlgebraicGeometry.Scheme.Modules
