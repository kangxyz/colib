/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodEvaluation
public import Colib.CategoryTheory.Sites.Point.NeighborhoodRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints

/-!
# Enough geometric neighborhood points on the original smooth étale site

For every point of every smooth separated finite-type object, mark the object
by the algebraic closure of its residue field, using native `GeometricPoint.ofPoint`.
The actual affine étale neighborhood points form a conservative family for the original smooth étale
topology. Consequently a morphism of ordinary abelian-group sheaves is an
isomorphism exactly when its maps on all geometric neighborhood values are
isomorphisms.

The point fibers and coefficients lie in universe `u + 1`, while schemes and
marking fields lie in universe `u`. This allows the family indexed by all
smooth objects and all their points, with no small-site replacement or
closed-point restriction. The quasi-separatedness of the base is precisely
the hypothesis used to keep affine neighborhoods in the smooth site.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [QuasiSeparatedSpace S]

/-- The actual neighborhood points at all points of all original smooth objects. -/
@[colib_tag "COL-1085", colib_ref "axiom_stacks_5ed82d14"
  "AlgebraicGeometry/EtaleCohomology/EnoughGeometricPoints.lean:66-69"
  "ingredient" "Native geometric points from algebraic closures of residue fields"]
def etaleNeighborhoodPointFamily (S : Scheme.{u}) [QuasiSeparatedSpace S] :
    ObjectProperty (etaleTopology S).Point.{u + 1} :=
  ObjectProperty.ofObj (fun (p : Σ X : SmoothSite S, X.left) ↦
    etaleNeighborhoodPoint.{u, u + 1} p.1 (GeometricPoint.ofPoint p.1.left p.2).hom)

/-- The family is small in the coefficient universe, including all smooth objects. -/
instance small_etaleNeighborhoodPointFamily (S : Scheme.{u}) [QuasiSeparatedSpace S] :
    ObjectProperty.Small.{u + 1} (etaleNeighborhoodPointFamily S) :=
  inferInstanceAs (ObjectProperty.Small.{u + 1} (ObjectProperty.ofObj _))

/-- The original smooth étale topology is detected by actual geometric neighborhoods. -/
@[colib_tag "COL-1085", stacks 00YK
  "Conservativity of the actual affine geometric neighborhood points of the smooth etale site"]
theorem isConservativeFamilyOfPoints_etaleNeighborhood (S : Scheme.{u})
    [QuasiSeparatedSpace S] :
    (etaleNeighborhoodPointFamily S).IsConservativeFamilyOfPoints := by
  apply ObjectProperty.IsConservativeFamilyOfPoints.mk'
  intro X R hR
  have hcover (x : X.left) : ∃ (Y : SmoothSite S) (f : Y ⟶ X),
      R f ∧ Etale f.left ∧ ∃ (y : Y.left), f.left y = x := by
    let ξ := (GeometricPoint.ofPoint X.left x).hom
    let D := etaleNeighborhoodToSmooth X ξ
    let := etaleNeighborhoodInitiallySmall.{u, u + 1} X ξ
    obtain ⟨A⟩ : Nonempty (EtaleNeighborhood X ξ) := IsCofiltered.nonempty
    let Φ : (etaleNeighborhoodPointFamily S).FullSubcategory :=
      ⟨etaleNeighborhoodPoint.{u, u + 1} X ξ,
        ObjectProperty.ofObj_apply _ (⟨X, x⟩ : Σ X : SmoothSite S, X.left)⟩
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
    change (etaleNeighborhoodMark X ξ B ≫ (etaleNeighborhoodHom X ξ B).left) default = x
    rw [etaleNeighborhoodMark_hom]
    exact GeometricPoint.ofPoint_liesOver X.left x
  choose Y f hf he y hy using hcover
  refine mem_etaleTopology_iff.mpr ⟨Presieve.ofArrows Y f, ?_, ?_⟩
  · exact (ofArrows_mem_etalePrecoverage_iff f).mpr ⟨he, fun x ↦ ⟨x, y x, hy x⟩⟩
  · rintro _ _ ⟨x⟩
    exact hf x

/-- The original smooth étale site has enough points at the coefficient universe. -/
@[colib_tag "COL-1085"]
instance etaleTopology_hasEnoughPoints_succ (S : Scheme.{u}) [QuasiSeparatedSpace S] :
    GrothendieckTopology.HasEnoughPoints.{u + 1} (etaleTopology S) where
  exists_objectProperty :=
    ⟨etaleNeighborhoodPointFamily S, inferInstance,
      isConservativeFamilyOfPoints_etaleNeighborhood S⟩

/-- A sheaf morphism is invertible if and only if it is invertible at every residue
geometric marking, with the original neighborhood maps on its underlying presheaf. -/
@[colib_tag "COL-1085"]
theorem isIso_iff_residueGeometricNeighborhoodValue
    {F G : Sheaf (etaleTopology S) AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    IsIso f ↔ ∀ (X : SmoothSite S) (x : X.left),
      IsIso ((etaleNeighborhoodPoint.{u, u + 1} X
        (GeometricPoint.ofPoint X.left x).hom).presheafFiber.map f.hom) := by
  rw [(isConservativeFamilyOfPoints_etaleNeighborhood S).jointlyReflectIsomorphisms
    AddCommGrpCat.{u + 1} |>.isIso_iff]
  constructor
  · intro h X x
    exact h ⟨_, ObjectProperty.ofObj_apply _ (⟨X, x⟩ : Σ X : SmoothSite S, X.left)⟩
  · rintro h ⟨Φ, ⟨⟨X, x⟩⟩⟩
    exact h X x

/-- Native algebraically closed geometric points jointly detect isomorphisms on the
original smooth site, using the same marked diagrams as the strict henselization comparison. -/
@[colib_tag "COL-1085"]
theorem isIso_iff_geometricEtaleNeighborhoodValue
    {F G : Sheaf (etaleTopology S) AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    IsIso f ↔ ∀ (X : SmoothSite S) (s : GeometricPoint X.left),
      IsIso ((etaleNeighborhoodPoint.{u, u + 1} X s.hom).presheafFiber.map f.hom) := by
  constructor
  · intro _ X s
    change IsIso ((etaleNeighborhoodPoint.{u, u + 1} X s.hom).sheafFiber.map f)
    infer_instance
  · intro h
    exact (isIso_iff_residueGeometricNeighborhoodValue f).mpr
      (fun X x ↦ h X (GeometricPoint.ofPoint X.left x))

/-- All separably closed field-valued markings jointly detect isomorphisms of
ordinary sheaves on the original smooth étale site. -/
@[colib_tag "COL-1085"]
theorem isIso_iff_etaleNeighborhoodValue
    {F G : Sheaf (etaleTopology S) AddCommGrpCat.{u + 1}} (f : F ⟶ G) :
    IsIso f ↔ ∀ (X : SmoothSite S) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (ξ : Spec (.of Ω) ⟶ X.left),
      IsIso ((etaleNeighborhoodPoint.{u, u + 1} X ξ).presheafFiber.map f.hom) := by
  constructor
  · intro _ X Ω _ _ ξ
    change IsIso ((etaleNeighborhoodPoint.{u, u + 1} X ξ).sheafFiber.map f)
    infer_instance
  · intro h
    apply (isIso_iff_residueGeometricNeighborhoodValue f).mpr
    exact fun X x ↦ h X (AlgebraicClosure (X.left.residueField x))
      (GeometricPoint.ofPoint X.left x).hom

end AlgebraicGeometry.Scheme.SmoothSite
