/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Presheaf.LiftingRelation

/-! # Original Laurent sections give elements in the canonical sheaf-map image -/
/-!
Adapted from `Motivic/Cohomology/A1/Boundary/Presheaf/LaurentImage.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `8b36a283c0d273fbfffb949f45721663c79a9e9d`. All generator and image-sieve maps use the
actual native Laurent cylinder and closed inverse-image boundary.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  (P : PresheafWithTransfers.{u + 1} k)

/-- Actual restriction of Laurent sections to the literal punctured cylinder neighborhoods. -/
def laurentToPunctured :
    (toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj
      (PresheafWithTransfers.torusSections P) ⟶
    (cylinderNeighborhood X).op ⋙
      (baseChange (SmoothSite.Contraction.openInclusion.app X).left).op ⋙
        (toSmoothSite (SmoothSite.Contraction.torusCylinder.obj X)).op ⋙
          (PresheafWithTransfers.toPresheaf k).obj P :=
  Functor.whiskerLeft (toSmoothSite X).op
      (PresheafWithTransfers.withParameterUnderlyingIso P (SmoothSite.multiplicativeGroupObject (Spec (.of k)))).hom ≫
    Functor.whiskerRight (NatTrans.op (puncturedProjectionNat X))
      ((PresheafWithTransfers.toPresheaf k).obj P)

/-- Canonical Laurent representatives expressed with the actual original generator map. -/
theorem laurent_generator_formula :
    laurentToAmbientCokernel X P ≫ ambientCokernelToBoundary X P =
      laurentToPunctured X P ≫
        Functor.whiskerLeft (cylinderNeighborhood X).op
          (presheafBoundaryGenerator ((PresheafWithTransfers.toPresheaf k).obj P)
            (SmoothSite.Contraction.openInclusion.app X) (SmoothSite.Contraction.nativeAffineSection (.of k) X 0)) ≫
        Functor.whiskerRight (NatTrans.op (zeroNeighborhoodLiftNat X))
          (zeroSectionBoundary X P).obj := by
  simp only [laurentToAmbientCokernel, ambientCokernelToBoundary, laurentToPunctured,
    presheafBoundaryGenerator, Functor.whiskerLeft_comp, Category.assoc]

/-- The original Laurent representative lies in the image after sheafifying the
original contraction, with its original quotient projection retained. -/
theorem laurent_boundary_mem_image (V : EtaleSeparatedFiniteType X.left)
    (a : ((PresheafWithTransfers.toPresheaf k).obj
      (PresheafWithTransfers.torusSections P)).obj (op ((toSmoothSite X).obj V))) :
    ∃ c, (contractionToBoundary X P).hom.app (op V) c =
      (ambientCokernelToBoundary X P).app (op V)
        ((laurentToAmbientCokernel X P).app (op V) a) := by
  refine ⟨(toSheafify (nisnevichTopology X.left)
    ((toSmoothSite X).op ⋙ (PresheafWithTransfers.toPresheaf k).obj
      (PresheafWithTransfers.contraction P))).app (op V)
    (((PresheafWithTransfers.toPresheaf k).map
      (PresheafWithTransfers.toContraction P)).app (op ((toSmoothSite X).obj V)) a), ?_⟩
  exact ConcreteCategory.congr_hom
    (congr_app (laurent_sheafified_boundary X P) (op V)) a

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary.OriginalPresheaf

