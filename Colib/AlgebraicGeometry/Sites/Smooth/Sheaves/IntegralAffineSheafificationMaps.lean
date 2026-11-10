/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Sheaves.IntegralAffineSheafification
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Sheafification maps from the actual integral affine basis

Maps between restrictions of arbitrary presheaves are first composed with the
actual target sheafification unit. Dense-subsite gluing and the sheafification
adjunction then produce ordinary sheaf maps. All coefficients remain in
`AddCommGrpCat.{u + 1}`. Surjectivity on integral affines gives a genuine covering
image sieve, and hence an epimorphism after ordinary sheafification.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

variable (k : Type u) [Field k]
  {A B C : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}

/-- Extend a map on the integral affine basis to actual ordinary sheafification. -/
def integralAffineSheafifyMap
    (α : (integralAffineInclusion k).op ⋙ A ⟶ (integralAffineInclusion k).op ⋙ B) :
    (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj A ⟶
      (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj B :=
  sheafifyIntegralAffineHom k
    (α ≫ (integralAffineInclusion k).op.whiskerLeft
      (toSheafify (nisnevichTopology (Spec (.of k))) B))

/-- The construction retains the prescribed map followed by the actual unit. -/
theorem integralAffineSheafifyMap_restrict
    (α : (integralAffineInclusion k).op ⋙ A ⟶ (integralAffineInclusion k).op ⋙ B) :
    (integralAffineInclusion k).op.whiskerLeft
      (toSheafify (nisnevichTopology (Spec (.of k))) A ≫
        (integralAffineSheafifyMap k α).hom) =
      α ≫ (integralAffineInclusion k).op.whiskerLeft
        (toSheafify (nisnevichTopology (Spec (.of k))) B) :=
  sheafifyIntegralAffineHom_restrict k _

/-- Maps out of actual sheafification are determined on the integral affine basis. -/
theorem integralAffineSheafifyHom_ext
    {G : Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}}
    (f g : (presheafToSheaf (nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).obj A ⟶ G)
    (h : (integralAffineInclusion k).op.whiskerLeft
        (toSheafify (nisnevichTopology (Spec (.of k))) A ≫ f.hom) =
      (integralAffineInclusion k).op.whiskerLeft
        (toSheafify (nisnevichTopology (Spec (.of k))) A ≫ g.hom)) : f = g := by
  exact (sheafifyIntegralAffineHom_unique k _ f h).trans
    (sheafifyIntegralAffineHom_unique k _ g rfl).symm

@[simp] theorem integralAffineSheafifyMap_id :
    integralAffineSheafifyMap k (𝟙 ((integralAffineInclusion k).op ⋙ A)) =
      𝟙 ((presheafToSheaf (nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).obj A) := by
  apply integralAffineSheafifyHom_ext k
  rw [integralAffineSheafifyMap_restrict]
  simp

@[simp] theorem integralAffineSheafifyMap_comp
    (α : (integralAffineInclusion k).op ⋙ A ⟶ (integralAffineInclusion k).op ⋙ B)
    (β : (integralAffineInclusion k).op ⋙ B ⟶ (integralAffineInclusion k).op ⋙ C) :
    integralAffineSheafifyMap k (α ≫ β) =
      integralAffineSheafifyMap k α ≫ integralAffineSheafifyMap k β := by
  apply integralAffineSheafifyHom_ext k
  rw [integralAffineSheafifyMap_restrict]
  symm
  calc
    _ = (integralAffineInclusion k).op.whiskerLeft
          (toSheafify (nisnevichTopology (Spec (.of k))) A ≫
            (integralAffineSheafifyMap k α).hom) ≫
        (integralAffineInclusion k).op.whiskerLeft
          (integralAffineSheafifyMap k β).hom := by
      change (integralAffineInclusion k).op.whiskerLeft
        (toSheafify (nisnevichTopology (Spec (.of k))) A ≫
          (integralAffineSheafifyMap k α).hom ≫
          (integralAffineSheafifyMap k β).hom) = _
      rw [← Category.assoc, Functor.whiskerLeft_comp]
    _ = α ≫ (integralAffineInclusion k).op.whiskerLeft
          (toSheafify (nisnevichTopology (Spec (.of k))) B ≫
            (integralAffineSheafifyMap k β).hom) := by
      rw [integralAffineSheafifyMap_restrict, Functor.whiskerLeft_comp, Category.assoc]
    _ = _ := by rw [integralAffineSheafifyMap_restrict, Category.assoc]

/-- On restricted ordinary maps this is exactly native ordinary sheafification. -/
@[simp] theorem integralAffineSheafifyMap_whisker (f : A ⟶ B) :
    integralAffineSheafifyMap k ((integralAffineInclusion k).op.whiskerLeft f) =
      (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).map f := by
  apply integralAffineSheafifyHom_ext k
  rw [integralAffineSheafifyMap_restrict]
  change _ = (integralAffineInclusion k).op.whiskerLeft
    (toSheafify (nisnevichTopology (Spec (.of k))) A ≫
      sheafifyMap (nisnevichTopology (Spec (.of k))) f)
  rw [← toSheafify_naturality, Functor.whiskerLeft_comp]

/-- The zero basis morphism gives the zero ordinary sheaf morphism. -/
@[simp] theorem integralAffineSheafifyMap_zero :
    integralAffineSheafifyMap k
      (0 : (integralAffineInclusion k).op ⋙ A ⟶ (integralAffineInclusion k).op ⋙ B) =
      0 := by
  have h : (integralAffineInclusion k).op.whiskerLeft (0 : A ⟶ B) = 0 := by
    ext X x
    rfl
  rw [← h, integralAffineSheafifyMap_whisker, Functor.map_zero]

/-- An actual basis isomorphism induces an actual ordinary sheaf isomorphism. -/
def integralAffineSheafifyIso
    (e : (integralAffineInclusion k).op ⋙ A ≅ (integralAffineInclusion k).op ⋙ B) :
    (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj A ≅
      (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj B where
  hom := integralAffineSheafifyMap k e.hom
  inv := integralAffineSheafifyMap k e.inv
  hom_inv_id := by rw [← integralAffineSheafifyMap_comp, e.hom_inv_id,
    integralAffineSheafifyMap_id]
  inv_hom_id := by rw [← integralAffineSheafifyMap_comp, e.inv_hom_id,
    integralAffineSheafifyMap_id]

/-- Integral affine surjectivity produces a genuine Nisnevich covering image sieve. -/
theorem isLocallySurjective_of_integral_affine_surjective (f : A ⟶ B)
    (hf : ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left],
      Function.Surjective (f.app (op X))) :
    Presheaf.IsLocallySurjective (nisnevichTopology (Spec (.of k))) f where
  imageSieve_mem {X} s := by
    apply sieve_mem_of_integral_affine_arrows k X
    intro U _ _ a
    exact hf U (B.map a.op s)

/-- Local surjectivity of the actual native sheafification map. -/
theorem isLocallySurjective_sheafifyMap_of_integral_affine_surjective (f : A ⟶ B)
    (hf : ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left],
      Function.Surjective (f.app (op X))) :
    Sheaf.IsLocallySurjective
      ((presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).map f) := by
  have := isLocallySurjective_of_integral_affine_surjective k f hf
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac
    (nisnevichTopology (Spec (.of k))) (toSheafify_naturality _ f).symm

/-- Surjectivity on genuine integral affine charts gives the actual sheafified epi. -/
theorem epi_sheafifyMap_of_integral_affine_surjective (f : A ⟶ B)
    (hf : ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left],
      Function.Surjective (f.app (op X))) :
    Epi ((presheafToSheaf (nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).map f) := by
  have := isLocallySurjective_sheafifyMap_of_integral_affine_surjective k f hf
  infer_instance

end AlgebraicGeometry.Scheme.SmoothSite
