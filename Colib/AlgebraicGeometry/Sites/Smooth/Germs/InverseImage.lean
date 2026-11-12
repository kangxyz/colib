/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Germs.SmallRelativeNeighborhood
public import Colib.AlgebraicGeometry.Morphisms.Etale.Fibers.ResidueFieldMap
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Field.Point.Neighborhood

/-!
Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Germs/InverseImage.lean`, blob
`004fd3cb7ec1f9a35b6169ae1fc8b74777e88afd`.

 # Original germs as evaluations of genuine small-site inverse images -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {B : Scheme.{u}} {U X : SmoothSite B}

/-- An auxiliary literal diagram colimit, used only to transport the equality of
its actual field-valued structure map. The endpoint remains the original germ. -/
def smallFieldDiagramColimit (F : (SmoothSite B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (K : Type u) [Field K] (t : Spec (.of K) ⟶ X.left) : AddCommGrpCat.{u + 1} := by
  let : HasColimitsOfSize.{u, u + 1} AddCommGrpCat.{u + 1} :=
    hasColimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} AddCommGrpCat.{u + 1}
  exact colimit ((Functor.Elements.π
    (MorphismProperty.Over.forget etaleSeparatedFiniteType ⊤ X.left ⋙
      coyoneda.obj (op (Over.mk t)))).op ⋙ (EtaleSeparatedFiniteType.toSmoothSite X).op ⋙ F)

/-- A factorization of the actual source residue-field point through a small-site
field object identifies the existing original germ with genuine inverse-image evaluation. -/
def originalGermInverseImageOfFactorization [IsAffine B]
    (F : Sheaf (nisnevichTopology B) AddCommGrpCat.{u + 1})
    (f : U ⟶ X) [Etale f.left] (u : U.left) {S : Scheme.{u}}
    (b : S ⟶ X.left) (q : Spec (U.left.residueField u) ⟶ S)
    [Etale q] [IsSeparated q] [QuasiCompact q]
    (h : q ≫ b = U.left.fromSpecResidueField u ≫ f.left) :
    (nisnevichPointFiberCocone U u F.obj).pt ≅
      ((EtaleSeparatedFiniteType.inverseImage b).obj
        ((EtaleSeparatedFiniteType.restrict X AddCommGrpCat).obj F)).obj.obj
          (op (EtaleSeparatedFiniteType.fieldObject (U.left.residueField u) q)) :=
  (RelativeNisnevichNeighborhood.smallOriginalFiberIso f u F.obj).symm ≪≫
    eqToIso (congrArg (smallFieldDiagramColimit F.obj (U.left.residueField u)) h.symm) ≪≫
    EtaleSeparatedFiniteType.fieldNeighborhoodInverseImageIso b (U.left.residueField u) q
      ((EtaleSeparatedFiniteType.restrict X AddCommGrpCat).obj F)


/-- At every point of every étale neighborhood, the original germ is evaluation of
inverse image at the base residue field. No closed-point or residue-isomorphism
hypothesis is imposed. Both residue-field maps are the native scheme maps. -/
def originalGermResidueInverseImageIso [IsAffine B]
    (F : Sheaf (nisnevichTopology B) AddCommGrpCat.{u + 1})
    (f : U ⟶ X) [Etale f.left] (u : U.left) :
    (nisnevichPointFiberCocone U u F.obj).pt ≅
      ((EtaleSeparatedFiniteType.inverseImage (X.left.fromSpecResidueField (f.left u))).obj
        ((EtaleSeparatedFiniteType.restrict X AddCommGrpCat).obj F)).obj.obj
          (op (EtaleSeparatedFiniteType.fieldObject (U.left.residueField u)
            (Spec.map (f.left.residueFieldMap u)))) :=
  originalGermInverseImageOfFactorization F f u
    (X.left.fromSpecResidueField (f.left u)) (Spec.map (f.left.residueFieldMap u))
    (f.left.SpecMap_residueFieldMap_fromSpecResidueField u)

end AlgebraicGeometry.Scheme.SmoothSite
