/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.GrothendieckGroup.Image
public import Colib.KTheory.Waldhausen.Fibration.Prespectrum
public import Colib.Topology.Prespectrum.MappingCone
public import Colib.Topology.Prespectrum.HomotopyTransport

/-!
# The original cone map to the actual image-quotient grading

The original exact functor's already normalized image has quotient grade zero. Its actual
zero-to-image transformation, reversed, nulls the composite with the original change of
weak equivalences. The resulting cone descent is unshifted and retains both its original
face and its whole cylinder. No stable equivalence or seed compatibility is assumed here.
-/

/-! Implementation provenance: `Quillen/Waldhausen/GrothendieckComparison/ImageQuotientCone.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, endpoint casts, complete homotopies and hypotheses are retained
under their native mathematical owners. -/
@[expose] public section

open CategoryTheory.Waldhausen.IteratedS

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u v
namespace CategoryTheory.Waldhausen.AlgebraicGrothendieck

open Topology
open IteratedS
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) {V : Structure D} (F : C ⥤ D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- The same original rebased functor used by the public exact prespectrum map. -/
abbrev imageQuotientNormalizedFunctor : C ⥤ D :=
  CategoryTheory.rebaseFunctor F W.zero V.zero ((hF.zero W.isZero).iso V.isZero)

/-- Normalization retains an actual original image witness, hence zero quotient grade. -/
theorem imageQuotientNormalizedFunctor_grade_zero (A : C) :
    (imageQuotientGrading W F hF).value
      ((imageQuotientNormalizedFunctor W F hF).obj A) = 0 := by
  apply imageQuotientGrading_zero_of_weakImage W F hF
  refine ⟨A, (CategoryTheory.rebaseFunctorIso F W.zero V.zero
    ((hF.zero W.isZero).iso V.isZero)).hom.app A, ?_⟩
  exact V.weq_iso _ inferInstance

/-- The literal zero-to-original-normalized-image transformation in the same target category. -/
def imageQuotientZeroToNormalized :
    zeroFunctor (C := C) (imageQuotientGrading W F hF).coarseStructure ⟶
      imageQuotientNormalizedFunctor W F hF ⋙ 𝟭 D where
  app A := V.isZero.to_ ((imageQuotientNormalizedFunctor W F hF).obj A)
  naturality _ _ _ := V.isZero.eq_of_src _ _

/-- The actual zero-to-image arrows are weak precisely by the original quotient relation. -/
theorem imageQuotientZeroToNormalized_weak (A : C) :
    (imageQuotientGrading W F hF).coarseStructure.weq
      ((imageQuotientZeroToNormalized W F hF).app A) :=
  (imageQuotientGrading W F hF).zero.trans
    (imageQuotientNormalizedFunctor_grade_zero W F hF A).symm

/-- Reversing the specified original zero-to-image track nulls the unchanged composite. -/
def imageQuotientPrespectrumNullhomotopy : LoopPrespectrum.Homotopy
    (exactOriginalPrespectrumMap W V hF ≫
      Fibration.changeWeakPrespectrumMap (imageQuotientGrading W F hF).nested)
    (LoopPrespectrum.zeroHom (originalPrespectrum W)
      (originalPrespectrum (imageQuotientGrading W F hF).coarseStructure)) := by
  let d := imageQuotientGrading W F hF
  let hG := hF.rebase.comp (Fibration.changeWeak_exact d.nested)
  have h0 : (imageQuotientNormalizedFunctor W F hF ⋙ 𝟭 D).obj W.zero =
      d.coarseStructure.zero := CategoryTheory.rebaseFunctor_obj_base _ _ _ _
  let H := (originalPrespectrumTransformationHomotopy W d.coarseStructure
    (zeroFunctor_isExact W d.coarseStructure) hG rfl h0
    (imageQuotientZeroToNormalized W F hF)
    (imageQuotientZeroToNormalized_weak W F hF)).symm
  have he : originalPrespectrumMap W d.coarseStructure hG h0 =
      exactOriginalPrespectrumMap W V hF ≫
        Fibration.changeWeakPrespectrumMap d.nested :=
    originalPrespectrumMap_comp W V d.coarseStructure hF.rebase
      (Fibration.changeWeak_exact d.nested)
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) d.nested.zero_eq.symm
  exact H.cast he (originalPrespectrumMap_zeroFunctor W d.coarseStructure)

/-- The literal cone of the original exact prespectrum map maps to the unshifted grading model. -/
def imageQuotientConeMap :
    LoopPrespectrum.mappingCone (exactOriginalPrespectrumMap W V hF) ⟶
      originalPrespectrum (imageQuotientGrading W F hF).coarseStructure :=
  LoopPrespectrum.mappingConeDesc (exactOriginalPrespectrumMap W V hF)
    (Fibration.changeWeakPrespectrumMap (imageQuotientGrading W F hF).nested)
    (imageQuotientPrespectrumNullhomotopy W F hF)

/-- The original cone face is exactly the original change of weak equivalences. -/
@[reassoc]
theorem imageQuotientConeMap_inclusion :
    LoopPrespectrum.mappingConeInclusion (exactOriginalPrespectrumMap W V hF) ≫
      imageQuotientConeMap W F hF =
        Fibration.changeWeakPrespectrumMap (imageQuotientGrading W F hF).nested :=
  LoopPrespectrum.mappingConeInclusion_desc _ _ _

end CategoryTheory.Waldhausen.AlgebraicGrothendieck
