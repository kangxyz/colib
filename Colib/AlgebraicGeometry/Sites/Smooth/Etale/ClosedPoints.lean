/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.EnoughPoints
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Closed geometric neighborhood points on the original smooth étale site

Over a quasi-separated Jacobson base, the native residue-field geometric points at closed
points of the original smooth objects form a conservative subfamily. In particular this
applies over the spectrum of any field, without an algebraic-closedness hypothesis or a
restriction to rational points.

The sieve proof first obtains an actual étale arrow through each closed point. Every point
specializes to a closed point by the Jacobson property, and an étale arrow has open image.
Thus these same arrows cover every point and generate a covering sieve in the original
smooth étale topology. Conservativity is not inferred merely from the larger all-point family.

The markings are the native algebraic closures of residue fields, and therefore are exactly
the markings admitted by the strict henselization comparison. Point fibers and ordinary
abelian-group coefficients remain in universe `u + 1`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [QuasiSeparatedSpace S]

/-- The actual neighborhood points indexed only by closed points of smooth objects. -/
@[colib_tag "COL-1095"]
def closedEtaleNeighborhoodPointFamily (S : Scheme.{u}) [QuasiSeparatedSpace S] :
    ObjectProperty (etaleTopology S).Point.{u + 1} :=
  ObjectProperty.ofObj (fun (p : Σ X : SmoothSite S, closedPoints X.left) ↦
    etaleNeighborhoodPoint.{u, u + 1} p.1 (GeometricPoint.ofPoint p.1.left p.2.1).hom)

/-- The closed-point family is small in the same coefficient universe as the all-point family. -/
instance small_closedEtaleNeighborhoodPointFamily (S : Scheme.{u}) [QuasiSeparatedSpace S] :
    ObjectProperty.Small.{u + 1} (closedEtaleNeighborhoodPointFamily S) :=
  inferInstanceAs (ObjectProperty.Small.{u + 1} (ObjectProperty.ofObj _))

/-- The closed-point family is a subfamily of the existing native all-point family. -/
theorem closedEtaleNeighborhoodPointFamily_le (S : Scheme.{u}) [QuasiSeparatedSpace S] :
    closedEtaleNeighborhoodPointFamily S ≤ etaleNeighborhoodPointFamily S := by
  rintro _ ⟨⟨X, x⟩⟩
  exact ObjectProperty.ofObj_apply _ (⟨X, x.1⟩ : Σ X : SmoothSite S, X.left)

omit [QuasiSeparatedSpace S] in
/-- Actual étale arrows of a sieve covering the closed points cover a Jacobson smooth object. -/
@[colib_tag "COL-1095", stacks 005U
  "Closed-point density in a Jacobson space promotes open etale images to a covering family"]
theorem mem_etaleTopology_of_covers_closedPoints {X : SmoothSite S} [JacobsonSpace X.left]
    (R : Sieve X)
    (hR : ∀ x : closedPoints X.left, ∃ (Y : SmoothSite S) (f : Y ⟶ X),
      R f ∧ Etale f.left ∧ ∃ y : Y.left, f.left y = x.1) :
    R ∈ etaleTopology S X := by
  choose Y f hf he y hy using hR
  refine mem_etaleTopology_iff.mpr ⟨Presieve.ofArrows Y f, ?_, ?_⟩
  · apply (ofArrows_mem_etalePrecoverage_iff f).mpr
    refine ⟨he, fun x ↦ ?_⟩
    obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
      (show (closure ({x} : Set X.left)).Nonempty from ⟨x, subset_closure (by simp)⟩)
      isClosed_closure.isLocallyClosed
    let z' : closedPoints X.left := ⟨z, hzc⟩
    let : Etale (f z').left := he z'
    have hx : x ∈ Set.range (f z').left :=
      (specializes_iff_mem_closure.mpr hz).mem_open (f z').left.isOpenMap.isOpen_range
        ⟨y z', hy z'⟩
    exact ⟨z', hx⟩
  · rintro _ _ ⟨x⟩
    exact hf x

/-- Closed residue-geometric neighborhood points detect the original smooth étale topology
over a Jacobson base, in particular over the spectrum of any field. -/
@[colib_tag "COL-1095", stacks 00YK
  "Conservativity of closed residue-geometric neighborhood points on the smooth etale site"]
theorem isConservativeFamilyOfPoints_closedEtaleNeighborhood (S : Scheme.{u})
    [QuasiSeparatedSpace S] [JacobsonSpace S] :
    (closedEtaleNeighborhoodPointFamily S).IsConservativeFamilyOfPoints := by
  apply ObjectProperty.IsConservativeFamilyOfPoints.mk'
  intro X R hR
  let : JacobsonSpace X.left :=
    LocallyOfFiniteType.jacobsonSpace (show X.left ⟶ S from X.hom)
  apply mem_etaleTopology_of_covers_closedPoints R
  intro x
  let ξ := (GeometricPoint.ofPoint X.left x.1).hom
  let D := etaleNeighborhoodToSmooth X ξ
  let := etaleNeighborhoodInitiallySmall.{u, u + 1} X ξ
  obtain ⟨A⟩ : Nonempty (EtaleNeighborhood X ξ) := IsCofiltered.nonempty
  let Φ : (closedEtaleNeighborhoodPointFamily S).FullSubcategory :=
    ⟨etaleNeighborhoodPoint.{u, u + 1} X ξ,
      ObjectProperty.ofObj_apply _ (⟨X, x⟩ : Σ X : SmoothSite S, closedPoints X.left)⟩
  obtain ⟨Z, g, hg, z, hz⟩ := hR Φ
    (GrothendieckTopology.Point.ofIsCofiltered.fiberMk.{u + 1}
      (p := D) (etaleNeighborhoodHom X ξ A))
  change (GrothendieckTopology.Point.ofIsCofiltered.fiber.{u + 1} D).map g z =
    GrothendieckTopology.Point.ofIsCofiltered.fiberMk.{u + 1}
      (etaleNeighborhoodHom X ξ A) at hz
  obtain ⟨B, q, hq⟩ :=
    GrothendieckTopology.Point.ofIsCofiltered.exists_mem_sieve_of_fiber_map_eq_fiberMk hg hz
  have hcomp : D.map q ≫ etaleNeighborhoodHom X ξ A = etaleNeighborhoodHom X ξ B :=
    MorphismProperty.Over.Hom.ext (etaleNeighborhoodMap_hom X ξ q)
  rw [hcomp] at hq
  refine ⟨D.obj B, etaleNeighborhoodHom X ξ B, hq, inferInstance,
    etaleNeighborhoodMark X ξ B default, ?_⟩
  change (etaleNeighborhoodMark X ξ B ≫ (etaleNeighborhoodHom X ξ B).left) default = x.1
  rw [etaleNeighborhoodMark_hom]
  exact GeometricPoint.ofPoint_liesOver X.left x.1

variable [JacobsonSpace S]

/-- Isomorphisms of ordinary abelian-group sheaves are detected at all closed points,
using the original native residue-geometric markings and neighborhood maps. -/
@[colib_tag "COL-1095"]
theorem isIso_iff_closedResidueGeometricNeighborhoodValue
    {F G : Sheaf (etaleTopology S) AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    IsIso f ↔ ∀ (X : SmoothSite S) (x : X.left), IsClosed ({x} : Set X.left) →
      IsIso ((etaleNeighborhoodPoint.{u, u + 1} X
        (GeometricPoint.ofPoint X.left x).hom).presheafFiber.map f.hom) := by
  rw [(isConservativeFamilyOfPoints_closedEtaleNeighborhood S).jointlyReflectIsomorphisms
    AddCommGrpCat.{u + 1} |>.isIso_iff]
  constructor
  · intro h X x hx
    exact h ⟨_, ObjectProperty.ofObj_apply _
      (⟨X, ⟨x, hx⟩⟩ : Σ X : SmoothSite S, closedPoints X.left)⟩
  · rintro h ⟨Φ, ⟨⟨X, x⟩⟩⟩
    exact h X x.1 x.2

/-- Native geometric markings whose image is closed jointly detect isomorphisms,
without requiring the closed points to be rational over the base field. -/
@[colib_tag "COL-1095"]
theorem isIso_iff_closedGeometricEtaleNeighborhoodValue
    {F G : Sheaf (etaleTopology S) AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    IsIso f ↔ ∀ (X : SmoothSite S) (s : GeometricPoint X.left),
      IsClosed ({s.hom default} : Set X.left) →
      IsIso ((etaleNeighborhoodPoint.{u, u + 1} X s.hom).presheafFiber.map f.hom) := by
  constructor
  · intro _ X s _
    change IsIso ((etaleNeighborhoodPoint.{u, u + 1} X s.hom).sheafFiber.map f)
    infer_instance
  · intro h
    apply (isIso_iff_closedResidueGeometricNeighborhoodValue f).mpr
    intro X x hx
    exact h X (GeometricPoint.ofPoint X.left x)
      (by simpa only [GeometricPoint.ofPoint_liesOver X.left x] using hx)

end AlgebraicGeometry.Scheme.SmoothSite
