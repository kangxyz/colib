/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Sheaves.IntegralAffineSheafIso
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Actual sheafification of maps extended from integral affines

After geometric dense-subsite extension, the native sheafification adjunction
gives a map out of actual ordinary Nisnevich sheafification. The unit formula
retains the given map on the integral affine basis. Coefficients are
`AddCommGrpCat.{u + 1}`, so native sheafification exists for this smooth site;
no sheafification, density, or exactness hypothesis is added.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (k : Type u) [Field k]
  {F : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
  {G : Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}}

/-- The ordinary sheaf map induced by a natural map on integral affine sources. -/
def sheafifyIntegralAffineHom
    (α : (integralAffineInclusion k).op ⋙ F ⟶
      (integralAffineInclusion k).op ⋙ G.obj) :
    (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj F ⟶ G where
  hom := sheafifyLift (nisnevichTopology (Spec (.of k)))
    (extendIntegralAffineHom k α) G.property

/-- The actual sheafification unit recovers the extended ordinary presheaf map. -/
@[reassoc (attr := simp)] theorem toSheafify_sheafifyIntegralAffineHom
    (α : (integralAffineInclusion k).op ⋙ F ⟶
      (integralAffineInclusion k).op ⋙ G.obj) :
    toSheafify (nisnevichTopology (Spec (.of k))) F ≫
      (sheafifyIntegralAffineHom k α).hom = extendIntegralAffineHom k α :=
  toSheafify_sheafifyLift _ _ _

/-- Restriction of the actual sheafification-unit composite is the given map. -/
theorem sheafifyIntegralAffineHom_restrict
    (α : (integralAffineInclusion k).op ⋙ F ⟶
      (integralAffineInclusion k).op ⋙ G.obj) :
    (integralAffineInclusion k).op.whiskerLeft
      (toSheafify (nisnevichTopology (Spec (.of k))) F ≫
        (sheafifyIntegralAffineHom k α).hom) = α := by
  rw [toSheafify_sheafifyIntegralAffineHom, extendIntegralAffineHom_restrict]

/-- The basis condition determines the actual ordinary sheaf map uniquely. -/
theorem sheafifyIntegralAffineHom_unique
    (α : (integralAffineInclusion k).op ⋙ F ⟶
      (integralAffineInclusion k).op ⋙ G.obj)
    (β : (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj F ⟶ G)
    (hβ : (integralAffineInclusion k).op.whiskerLeft
      (toSheafify (nisnevichTopology (Spec (.of k))) F ≫ β.hom) = α) :
    β = sheafifyIntegralAffineHom k α := by
  ext1
  apply sheafifyLift_unique
  exact extendIntegralAffineHom_unique k α _ hβ

end AlgebraicGeometry.Scheme.SmoothSite
