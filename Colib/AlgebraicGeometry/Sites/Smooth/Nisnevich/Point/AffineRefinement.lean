/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.NeighborhoodPoint
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Basic

/-!
# Affine refinement of smooth pointed étale neighborhoods

The affine Nisnevich neighborhoods refine the pointed étale neighborhoods
inside the smooth site. The inclusion preserves the actual neighborhood
scheme, structure map and marking. It compares the two presheaf fiber
colimits through their actual affine restriction diagrams.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} (X : SmoothSite S) (x : X.left)

private abbrev pointedEtaleFiber : X.left.Etale ⥤ Type u :=
  Scheme.Etale.forget X.left ⋙ coyoneda.obj (op (Over.mk (X.left.fromSpecResidueField x)))

private abbrev affinePointedEtaleFunctor :
    NisnevichNeighborhood X x ⥤ PointedEtaleNeighborhood X x :=
  Functor.Elements.precomp (AffineEtale.Spec X.left) (pointedEtaleFiber X x)

private def affinePointedEtaleFullyFaithful : (affinePointedEtaleFunctor X x).FullyFaithful where
  preimage f := Functor.Elements.homMk ((AffineEtale.Spec X.left).preimage f.hom) (by
    change (pointedEtaleFiber X x).map
      ((AffineEtale.Spec X.left).map ((AffineEtale.Spec X.left).preimage f.hom)) _ = _
    rw [Functor.map_preimage]
    exact f.map_val)
  map_preimage f := by
    apply Functor.Elements.hom_ext
    change (AffineEtale.Spec X.left).map ((AffineEtale.Spec X.left).preimage f.hom) = f.hom
    exact (AffineEtale.Spec X.left).map_preimage f.hom
  preimage_map f := Functor.Elements.hom_ext (Functor.preimage_map f.hom)

/-- Include the existing affine pointed neighborhoods with their actual maps. -/
def affineNisnevichNeighborhoodInclusion [QuasiSeparatedSpace S] :
    NisnevichNeighborhood X x ⥤ SmoothPointedEtaleNeighborhood X x :=
  (smoothNeighborhoodProperty X x).lift
    (Functor.Elements.precomp (AffineEtale.Spec X.left)
      (Scheme.Etale.forget X.left ⋙ coyoneda.obj (op (Over.mk (X.left.fromSpecResidueField x)))))
    fun A => by
      change smoothSeparatedFiniteType (A.obj.hom ≫ X.hom)
      exact ((nisnevichNeighborhoodToSmooth X x).obj A).prop

/-- The two smooth-site diagrams agree on the actual affine neighborhoods. -/
def affineNisnevichNeighborhoodDiagramIso [QuasiSeparatedSpace S] :
    affineNisnevichNeighborhoodInclusion X x ⋙ nisnevichNeighborhoodFunctor X x ≅
      nisnevichNeighborhoodToSmooth X x :=
  Iso.refl _

/-- Affine refinements are coinitial in the full smooth pointed diagram. -/
instance affineNisnevichNeighborhoodInclusion_initial [IsAffine S] :
    (affineNisnevichNeighborhoodInclusion X x).Initial := by
  let J := affineNisnevichNeighborhoodInclusion X x
  let hJ : (J ⋙ (smoothNeighborhoodProperty X x).ι).FullyFaithful :=
    affinePointedEtaleFullyFaithful X x
  let h := Functor.FullyFaithful.ofCompFaithful hJ
  let : J.Full := h.full
  let : J.Faithful := h.faithful
  change J.Initial
  apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  intro N
  let p := N.obj.obj.hom
  let l := N.obj.val.left
  let : Etale p := N.obj.obj.prop
  obtain ⟨A, a, ha, hl⟩ :=
    exists_nisnevichNeighborhood_refinement X x p l (Over.w N.obj.val)
  exact ⟨A, ⟨ObjectProperty.homMk (Functor.Elements.homMk
    (MorphismProperty.Over.homMk a ha) (Over.OverMorphism.ext hl))⟩⟩

/-- The full smooth pointed diagram computes the existing affine point fiber. -/
def smoothPointedEtaleFiberIso [IsAffine S] {A : Type v} [Category.{w} A]
    [HasColimitsOfSize.{u + 1, u + 1} A] (P : (SmoothSite S)ᵒᵖ ⥤ A) :
    (nisnevichPoint X x).presheafFiber.obj P ≅
      (nisnevichNeighborhoodPoint.{u, u + 1} X x).presheafFiber.obj P := by
  let J := affineNisnevichNeighborhoodInclusion X x
  let : J.Initial := affineNisnevichNeighborhoodInclusion_initial X x
  let D := nisnevichNeighborhoodFunctor X x
  let E := nisnevichNeighborhoodToSmooth X x
  let t := nisnevichPointFiberCocone X x P
  let e₀ : (J ⋙ D).op ≅ E.op := NatIso.op (affineNisnevichNeighborhoodDiagramIso X x).symm
  let e : J.op ⋙ (D.op ⋙ P) ≅ E.op ⋙ P :=
    (Functor.associator J.op D.op P).symm ≪≫
      Functor.isoWhiskerRight (Functor.opComp J D).symm P ≪≫
      Functor.isoWhiskerRight e₀ P
  have ht := (Functor.Final.isColimitWhiskerEquiv J.op t).symm
    (isColimitNisnevichPointFiberCocone X x P)
  have ht' := (IsColimit.precomposeInvEquiv e (t.whisker J.op)).symm ht
  let := nisnevichNeighborhoodInitiallySmall.{u, u + 1} X x
  exact ht'.coconePointUniqueUpToIso
    (GrothendieckTopology.Point.isColimitPresheafFiberOfIsCofilteredCocone.{u + 1}
      E (nisnevichNeighborhoodCoverLift X x) P)

end AlgebraicGeometry.Scheme.SmoothSite

end
