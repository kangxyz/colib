/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.Contraction.Basic
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.SheafComparison

/-! # The canonical original-presheaf contraction boundary specializes to sheaves -/

/-!
Adapted from `Motivic/Cohomology/A1/Boundary/Contraction/SheafComparison.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `b9d62c5b69057b29d61d4f0a7ed4646f3b5333be`.
The actual native additive and multiplicative parameter objects and the existing
small-site image adjunction are retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (F : SheafWithTransfers.{u + 1} k)

/-- The two actual zero-section boundary objects agree for a coefficient sheaf. -/
def zeroSectionBoundarySheafIso :
    zeroSectionBoundary X F.obj ≅ Boundary.zeroSectionBoundary X F :=
  presheafBoundarySheafIso ((SheafWithTransfers.toSheaf k).obj F)
    (SmoothSite.Contraction.openInclusion.app X) (SmoothSite.Contraction.nativeAffineSection (.of k) X 0)

/-- The original Laurent projection commutes with the ambient sheaf comparison. -/
@[reassoc (attr := simp)]
theorem laurentToAmbientCokernel_sheafIso :
    laurentToAmbientCokernel X F.obj ≫ Functor.whiskerLeft (cylinderNeighborhood X).op
        (presheafBoundaryAmbientSheafIso ((SheafWithTransfers.toSheaf k).obj F)
          (SmoothSite.Contraction.openInclusion.app X)).hom.hom =
      Boundary.laurentToAmbientCokernel X F := by
  unfold laurentToAmbientCokernel Boundary.laurentToAmbientCokernel
  rw [Category.assoc, Category.assoc, ← Functor.whiskerLeft_comp]
  exact congrArg (fun g =>
    Functor.whiskerLeft (toSmoothSite X).op
        (PresheafWithTransfers.withParameterUnderlyingIso F.obj (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom ≫
      Functor.whiskerRight (NatTrans.op (puncturedProjectionNat X))
        ((SheafWithTransfers.toSheaf k).obj F).obj ≫
      Functor.whiskerLeft (cylinderNeighborhood X).op g)
    (presheafBoundaryProjection_sheafIso ((SheafWithTransfers.toSheaf k).obj F)
      (SmoothSite.Contraction.openInclusion.app X))

/-- Naturality of the actual inverse-image unit and original zero lift gives the
boundary comparison square on ambient cylinder neighborhoods. -/
theorem ambientCokernelToBoundary_sheafIso :
    Functor.whiskerLeft (cylinderNeighborhood X).op
        (presheafBoundaryAmbientSheafIso ((SheafWithTransfers.toSheaf k).obj F)
          (SmoothSite.Contraction.openInclusion.app X)).hom.hom ≫
      Boundary.ambientCokernelToBoundary X F =
        ambientCokernelToBoundary X F.obj ≫ (zeroSectionBoundarySheafIso X F).hom.hom := by
  let e := presheafBoundaryAmbientSheafIso ((SheafWithTransfers.toSheaf k).obj F)
    (SmoothSite.Contraction.openInclusion.app X)
  let z := (SmoothSite.Contraction.nativeAffineSection (.of k) X 0).left
  apply NatTrans.ext
  funext V
  let A := presheafBoundaryAmbient ((SheafWithTransfers.toSheaf k).obj F).obj
    (SmoothSite.Contraction.openInclusion.app X)
  let C := boundaryAmbientCokernel ((SheafWithTransfers.toSheaf k).obj F)
    (SmoothSite.Contraction.openInclusion.app X)
  let W := op ((cylinderNeighborhood X).obj V.unop)
  let T := op ((zeroNeighborhood X).obj V.unop)
  have h : e.hom.hom.app W ≫ ((imageAdjunction z).unit.app C).hom.app W =
      ((imageAdjunction z).unit.app A).hom.app W ≫
        (zeroSectionBoundarySheafIso X F).hom.hom.app T :=
    congr_app (congrArg (fun f => f.hom) ((imageAdjunction z).unit.naturality e.hom)) W
  have hz := (zeroSectionBoundarySheafIso X F).hom.hom.naturality
    (zeroNeighborhoodLift X V.unop).op
  change e.hom.hom.app W ≫
      (((imageAdjunction z).unit.app C).hom.app W ≫
        (Boundary.zeroSectionBoundary X F).obj.map (zeroNeighborhoodLift X V.unop).op) =
    (((imageAdjunction z).unit.app A).hom.app W ≫
      (zeroSectionBoundary X F.obj).obj.map (zeroNeighborhoodLift X V.unop).op) ≫
        (zeroSectionBoundarySheafIso X F).hom.hom.app V
  rw [← Category.assoc, h, Category.assoc, ← hz, ← Category.assoc]

/-- The original contraction representatives induce the same canonical boundary
map after the explicit target comparison. -/
@[reassoc (attr := simp)]
theorem contractionToBoundaryPresheaf_sheafIso :
    contractionToBoundaryPresheaf X F.obj ≫ (zeroSectionBoundarySheafIso X F).hom.hom =
      Boundary.contractionToBoundaryPresheaf X F := by
  unfold contractionToBoundaryPresheaf Boundary.contractionToBoundaryPresheaf
  simp only [Category.assoc]
  apply congrArg (fun f => (contractionRestrictedCokernelIso X F.obj).hom ≫ f)
  apply (cancel_epi (cokernel.π (contractionRestrictionSmall X F.obj))).mp
  simp only [cokernel.π_desc_assoc]
  rw [← ambientCokernelToBoundary_sheafIso,
    ← Category.assoc, laurentToAmbientCokernel_sheafIso]

/-- Small sheafification of the original contraction agrees with the original
restricted contraction sheaf. Ordinary HI is used only to make that source a sheaf. -/
def contractionSheafIso (hF : F.obj.IsA1Invariant) :
    (presheafToSheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1}).obj
        ((toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj
          (PresheafWithTransfers.contraction F.obj)) ≅
      (restrict X AddCommGrpCat).obj
        ((SheafWithTransfers.toSheaf k).obj (SheafWithTransfers.contraction F hF)) :=
  (sheafificationIso ((restrict X AddCommGrpCat).obj
    ((SheafWithTransfers.toSheaf k).obj (SheafWithTransfers.contraction F hF)))).symm

/-- Both explicit object comparisons preserve the canonical boundary morphism. -/
theorem contractionToBoundary_sheafIso (hF : F.obj.IsA1Invariant) :
    contractionToBoundary X F.obj ≫ (zeroSectionBoundarySheafIso X F).hom =
      (contractionSheafIso X F hF).hom ≫ Boundary.contractionToBoundary X F hF := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (nisnevichTopology X.left) _ _
    (Boundary.zeroSectionBoundary X F).property
  change toSheafify (nisnevichTopology X.left) _ ≫
      ((contractionToBoundary X F.obj).hom ≫ (zeroSectionBoundarySheafIso X F).hom.hom) =
    toSheafify (nisnevichTopology X.left) _ ≫
      ((contractionSheafIso X F hF).hom.hom ≫
        (Boundary.contractionToBoundary X F hF).hom)
  rw [toSheafify_contractionToBoundary_assoc, contractionToBoundaryPresheaf_sheafIso]
  let G := (restrict X AddCommGrpCat).obj
    ((SheafWithTransfers.toSheaf k).obj (SheafWithTransfers.contraction F hF))
  have hS : toSheafify (nisnevichTopology X.left) G.obj ≫
      (contractionSheafIso X F hF).hom.hom = 𝟙 G.obj :=
    (isoSheafify (nisnevichTopology X.left) G.property).hom_inv_id
  rw [← Category.assoc]
  exact ((congrArg (fun f => f ≫ (Boundary.contractionToBoundary X F hF).hom) hS).trans
    (Category.id_comp _)).symm

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf

