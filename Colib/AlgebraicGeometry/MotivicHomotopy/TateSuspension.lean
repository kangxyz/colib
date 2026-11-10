/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSphere
public import Colib.CategoryTheory.Sites.Simplicial.MappingCofiber

/-!
# The strict roof for the Tate suspension

The common source attaches the simplicial reduced cone to the pointed
Laurent-open map. Collapsing the cone gives the open-complement quotient.
Collapsing the pointed affine line gives the reduced simplicial
suspension of the torus. The two local equivalence proofs belong to
the homotopical comparison of this roof.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry.MotivicHomotopy

open Scheme
open CategoryTheory.PointedSimplicialPresheaf

variable (R : CommRingCat.{u})

/-- The common source for the two strict comparison maps of the Tate suspension. -/
abbrev tateCone : PointedSimplicialPresheaf.{u} (SmoothSite (Spec R)) :=
  reducedMappingCofiber (pointedLaurentOpen R)

/-- The reduced simplicial suspension of the actual pointed torus, as a mapping cofiber. -/
abbrev simplicialTorusSuspension : PointedSimplicialPresheaf.{u} (SmoothSite (Spec R)) :=
  reducedMappingCofiber (toPoint (SmoothSite (Spec R)) (pointedTorus R))

/-- Collapsing the attached cone gives the actual Tate quotient. -/
def tateConeToSphere : tateCone R ⟶ tateSphere R :=
  pushout.desc (toTateSphere R)
    (toPoint (SmoothSite (Spec R)) (reducedCone (pointedTorus R)) ≫ tateSpherePoint R) (by
      rw [tateSphere_condition, ← Category.assoc]
      exact congrArg (fun f ↦ f ≫ tateSpherePoint R) ((point_isZero _).eq_of_tgt _ _))

@[reassoc (attr := simp)]
theorem toTateCone_tateConeToSphere :
    toReducedMappingCofiber (pointedLaurentOpen R) ≫ tateConeToSphere R = toTateSphere R :=
  pushout.inl_desc _ _ _

/-- Collapsing the affine-line term gives the reduced simplicial suspension. -/
def tateConeToSuspension : tateCone R ⟶ simplicialTorusSuspension R :=
  reducedMappingCofiberMap
    (Arrow.homMk (f := Arrow.mk (pointedLaurentOpen R))
      (g := Arrow.mk (toPoint (SmoothSite (Spec R)) (pointedTorus R)))
      (𝟙 _) (toPoint (SmoothSite (Spec R)) (pointedAffineLine R))
      ((point_isZero _).eq_of_tgt _ _))

end AlgebraicGeometry.MotivicHomotopy

attribute [colib_tag "COL-0386"]
  AlgebraicGeometry.MotivicHomotopy.tateConeToSphere
  AlgebraicGeometry.MotivicHomotopy.tateConeToSuspension
attribute [colib_ref "MorelVoevodsky1999" "Section 3.2, Lemma 2.15, p. 111" "ingredient"
  "The strict cone roof underlying the localized sphere comparison"]
  AlgebraicGeometry.MotivicHomotopy.tateConeToSuspension
