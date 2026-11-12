/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.ClosedPoints

/-!
# Conservative closed geometric points on affine smooth objects

Over an affine Jacobson base, it suffices to use the closed residue-geometric
markings on affine objects of the original smooth site. An affine open around
an arbitrary closed point has the same closed point. Its actual neighborhood
germs, composed with that open immersion, detect covering sieves on the
original object. This avoids assuming an affine presentation of every smooth
object or an unproved comparison of geometric neighborhood points.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [QuasiSeparatedSpace S]

/-- Native residue-geometric points at closed points of affine smooth objects. -/
def affineClosedEtaleNeighborhoodPointFamily (S : Scheme.{u}) [QuasiSeparatedSpace S] :
    ObjectProperty (etaleTopology S).Point.{u + 1} :=
  ObjectProperty.ofObj (fun
    (p : Σ X : {X : SmoothSite S // IsAffine X.left}, closedPoints X.1.left) ↦
      etaleNeighborhoodPoint.{u, u + 1} p.1.1
        (GeometricPoint.ofPoint p.1.1.left p.2.1).hom)

instance small_affineClosedEtaleNeighborhoodPointFamily (S : Scheme.{u})
    [QuasiSeparatedSpace S] :
    ObjectProperty.Small.{u + 1} (affineClosedEtaleNeighborhoodPointFamily S) :=
  inferInstanceAs (ObjectProperty.Small.{u + 1} (ObjectProperty.ofObj _))

omit [QuasiSeparatedSpace S] in
/-- Affine closed geometric neighborhood points already detect the full smooth étale topology. -/
@[stacks 00YK "Conservativity via affine-open germs at original closed points"]
theorem isConservativeFamilyOfPoints_affineClosedEtaleNeighborhood
    (S : Scheme.{u}) [IsAffine S] [JacobsonSpace S] :
    (affineClosedEtaleNeighborhoodPointFamily S).IsConservativeFamilyOfPoints := by
  apply ObjectProperty.IsConservativeFamilyOfPoints.mk'
  intro X R hR
  let : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace (show X.left ⟶ S from X.hom)
  apply mem_etaleTopology_of_covers_closedPoints R
  intro x
  obtain ⟨u, hu⟩ := X.left.affineCover.covers x.1
  let j := X.left.affineCover.f (X.left.affineCover.idx x.1)
  let : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion (X.left.affineCover.f (X.left.affineCover.idx x.1)))
  let U : SmoothSite S := mk (j ≫ X.hom)
  let f : U ⟶ X := homMk j rfl
  let : IsAffine U.left := inferInstanceAs (IsAffine (X.left.affineCover.X _))
  have huc : IsClosed ({u} : Set U.left) := by
    have he : j ⁻¹' ({x.1} : Set X.left) = ({u} : Set U.left) := by
      ext v
      change j v = x.1 ↔ v = u
      constructor
      · intro hv
        exact j.isOpenEmbedding.injective (hv.trans hu.symm)
      · rintro rfl
        exact hu
    rw [← he]
    exact x.2.preimage j.continuous
  let ξ := (GeometricPoint.ofPoint U.left u).hom
  let D := etaleNeighborhoodToSmooth U ξ
  let := etaleNeighborhoodInitiallySmall.{u, u + 1} U ξ
  obtain ⟨A⟩ : Nonempty (EtaleNeighborhood U ξ) := IsCofiltered.nonempty
  let Φ : (affineClosedEtaleNeighborhoodPointFamily S).FullSubcategory :=
    ⟨etaleNeighborhoodPoint.{u, u + 1} U ξ,
      ObjectProperty.ofObj_apply _
        (⟨⟨U, inferInstance⟩, ⟨u, huc⟩⟩ :
          Σ X : {X : SmoothSite S // IsAffine X.left}, closedPoints X.1.left)⟩
  obtain ⟨Z, g, hg, z, hz⟩ := hR Φ
    (GrothendieckTopology.Point.ofIsCofiltered.fiberMk.{u + 1}
      (p := D) (etaleNeighborhoodHom U ξ A ≫ f))
  change (GrothendieckTopology.Point.ofIsCofiltered.fiber.{u + 1} D).map g z =
    GrothendieckTopology.Point.ofIsCofiltered.fiberMk.{u + 1}
      (etaleNeighborhoodHom U ξ A ≫ f) at hz
  obtain ⟨B, q, hq⟩ :=
    GrothendieckTopology.Point.ofIsCofiltered.exists_mem_sieve_of_fiber_map_eq_fiberMk hg hz
  have hcomp : D.map q ≫ (etaleNeighborhoodHom U ξ A ≫ f) =
      etaleNeighborhoodHom U ξ B ≫ f := by
    rw [← Category.assoc]
    congr 1
    exact MorphismProperty.Over.Hom.ext (etaleNeighborhoodMap_hom U ξ q)
  rw [hcomp] at hq
  refine ⟨D.obj B, etaleNeighborhoodHom U ξ B ≫ f, hq, ?_,
    etaleNeighborhoodMark U ξ B default, ?_⟩
  · change Etale ((etaleNeighborhoodHom U ξ B).left ≫ j)
    infer_instance
  · change j ((etaleNeighborhoodMark U ξ B ≫
      (etaleNeighborhoodHom U ξ B).left) default) = x.1
    rw [etaleNeighborhoodMark_hom]
    exact (congrArg j (GeometricPoint.ofPoint_liesOver U.left u)).trans hu

omit [QuasiSeparatedSpace S] in
/-- Isomorphisms of actual sheaves are detected on affine closed residue-geometric markings. -/
theorem isIso_iff_affineClosedResidueGeometricNeighborhoodValue
    {S : Scheme.{u}} [IsAffine S] [JacobsonSpace S]
    {F G : Sheaf (etaleTopology S) AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    IsIso f ↔ ∀ (X : SmoothSite S) [IsAffine X.left] (x : X.left),
      IsClosed ({x} : Set X.left) →
        IsIso ((etaleNeighborhoodPoint.{u, u + 1} X
          (GeometricPoint.ofPoint X.left x).hom).presheafFiber.map f.hom) := by
  rw [(isConservativeFamilyOfPoints_affineClosedEtaleNeighborhood S).jointlyReflectIsomorphisms
    AddCommGrpCat.{u + 1} |>.isIso_iff]
  constructor
  · intro h X _ x hx
    exact h ⟨_, ObjectProperty.ofObj_apply _
      (⟨⟨X, inferInstance⟩, ⟨x, hx⟩⟩ :
        Σ X : {X : SmoothSite S // IsAffine X.left}, closedPoints X.1.left)⟩
  · rintro h ⟨Φ, ⟨⟨⟨X, hX⟩, x⟩⟩⟩
    let := hX
    exact h X x.1 x.2

omit [QuasiSeparatedSpace S] in
/-- Arbitrary separably closed markings with closed image on affine smooth objects suffice. -/
theorem isIso_iff_affineClosedEtaleNeighborhoodValue
    {S : Scheme.{u}} [IsAffine S] [JacobsonSpace S]
    {F G : Sheaf (etaleTopology S) AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    IsIso f ↔ ∀ (X : SmoothSite S) [IsAffine X.left]
      (Ω : Type u) [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X.left),
      IsClosed ({ξ default} : Set X.left) →
        IsIso ((etaleNeighborhoodPoint.{u, u + 1} X ξ).presheafFiber.map f.hom) := by
  constructor
  · intro _ X _ Ω _ _ ξ _
    change IsIso ((etaleNeighborhoodPoint.{u, u + 1} X ξ).sheafFiber.map f)
    infer_instance
  · intro h
    apply (isIso_iff_affineClosedResidueGeometricNeighborhoodValue f).mpr
    intro X _ x hx
    have he : (GeometricPoint.ofPoint X.left x).hom default = x :=
      GeometricPoint.ofPoint_liesOver X.left x
    exact h X (GeometricPoint.ofPoint X.left x).residueField
      (GeometricPoint.ofPoint X.left x).hom (by rw [he]; exact hx)

end AlgebraicGeometry.Scheme.SmoothSite
