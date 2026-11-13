/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.A1Prespectrum
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.Yoneda

/-!
# Represented bonding maps for Tate suspension

The suspension comparison on the original presheaf maps determines
a unique Tate bonding map from a natural operation on the represented
cohomology of the original pointed simplicial presheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PointedSimplicialPresheaf Opposite
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

local notation "Cᵣ" => SmoothSite (Spec R)
local notation "Jᵣ" => SmoothSite.nisnevichTopology (Spec R)
local notation "Iᵣ" => affineLineInterval (Spec R)
local notation "Q" => toAffineLineHomotopyCategory (Spec R)
local notation "F" => motivicTateSuspension R
local notation "P" => tatePresheafSuspension R

variable (A B : AffineLineHomotopyCategory (Spec R))

/-- Comparison of the suspended source with the localization of its actual Tate smash. -/
def tateSuspensionHomComparison (X : PointedSimplicialPresheaf.{u + 1} Cᵣ) :
    ((F).obj ((Q).obj X) ⟶ B) ≃ ((Q).obj ((P).obj X) ⟶ B) :=
  ((tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)).app X).homFromEquiv

variable (b : ∀ X : PointedSimplicialPresheaf.{u + 1} (SmoothSite (Spec R)),
    ((toAffineLineHomotopyCategory (Spec R)).obj X ⟶ A) →
      ((toAffineLineHomotopyCategory (Spec R)).obj ((tatePresheafSuspension R).obj X) ⟶ B))

private def strictBondingTransformation
    (h : ∀ {X Y : PointedSimplicialPresheaf.{u + 1} Cᵣ} (f : X ⟶ Y)
      (g : (Q).obj Y ⟶ A), b X ((Q).map f ≫ g) = (Q).map ((P).map f) ≫ b Y g) :
    (Q).op ⋙ yoneda.obj A ⟶ (Q).op ⋙ ((F).op ⋙ yoneda.obj B) := by
  let α := tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)
  refine ⟨fun X ↦ ↾(fun g ↦ α.hom.app X.unop ≫ b X.unop g), ?_⟩
  intro X Y f
  ext g
  change α.hom.app Y.unop ≫ b Y.unop ((Q).map f.unop ≫ g) =
    (F).map ((Q).map f.unop) ≫ α.hom.app X.unop ≫ b X.unop g
  have hα : (F).map ((Q).map f.unop) ≫ α.hom.app X.unop =
      α.hom.app Y.unop ≫ (Q).map ((P).map f.unop) := α.hom.naturality f.unop
  rw [h, ← Category.assoc, ← hα, Category.assoc]

variable
  (h : ∀ {X Y : PointedSimplicialPresheaf.{u + 1} (SmoothSite (Spec R))} (f : X ⟶ Y)
    (g : (toAffineLineHomotopyCategory (Spec R)).obj Y ⟶ A),
    b X ((toAffineLineHomotopyCategory (Spec R)).map f ≫ g) =
      (toAffineLineHomotopyCategory (Spec R)).map ((tatePresheafSuspension R).map f) ≫ b Y g)

private def bondingTransformation : yoneda.obj A ⟶ (F).op ⋙ yoneda.obj B :=
  (Localization.fullyFaithfulWhiskeringLeft (Q).op
    (intervalWeakEquivalences.{u + 1} Cᵣ Jᵣ Iᵣ).op (Type (u + 2))).preimage
    (strictBondingTransformation R A B b h)

/-- The Tate bonding map represented by the specified natural operation. -/
@[no_expose]
def tateBondingMap : (F).obj A ⟶ B :=
  yonedaEquiv (bondingTransformation R A B b h)

/-- The bonding map acts by the given operation, with the original Tate
smash comparison on the source of the map. -/
theorem tateBondingMap_comp (X : PointedSimplicialPresheaf.{u + 1} Cᵣ)
    (g : (Q).obj X ⟶ A) :
    (F).map g ≫ tateBondingMap R A B b h =
      (tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)).hom.app X ≫ b X g := by
  let H := Localization.fullyFaithfulWhiskeringLeft (Q).op
    (intervalWeakEquivalences.{u + 1} Cᵣ Jᵣ Iᵣ).op (Type (u + 2))
  let γ := strictBondingTransformation R A B b h
  let τ := bondingTransformation R A B b h
  have ht : ((Functor.whiskeringLeft _ _ _).obj (Q).op).map τ = γ := H.map_preimage γ
  have hx : τ.app (op ((Q).obj X)) = γ.app (op X) := NatTrans.congr_app ht (op X)
  have hg : τ.app (op ((Q).obj X)) g =
      (tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)).hom.app X ≫ b X g :=
    ConcreteCategory.congr_hom hx g
  have hy : ((F).op ⋙ yoneda.obj B).map g.op (yonedaEquiv τ) =
      τ.app (op ((Q).obj X)) g := by
    have hn := ConcreteCategory.congr_hom (τ.naturality g.op) (𝟙 A)
    change τ.app (op ((Q).obj X)) (g ≫ 𝟙 A) =
      ((F).op ⋙ yoneda.obj B).map g.op (yonedaEquiv τ) at hn
    rw [Category.comp_id] at hn
    exact hn.symm
  exact hy.trans hg

/-- The represented bonding map takes the original strict source
cohomology class to the original operation on its Tate smash. -/
theorem tateSuspensionHomComparison_tateBondingMap
    (X : PointedSimplicialPresheaf.{u + 1} Cᵣ) (g : (Q).obj X ⟶ A) :
    tateSuspensionHomComparison R B X ((F).map g ≫ tateBondingMap R A B b h) = b X g := by
  let α := (tateA1SuspensionCompIso R (tateStalkwiseAdjunction R)).app X
  change α.inv ≫ ((F).map g ≫ tateBondingMap R A B b h) = b X g
  have hg : (F).map g ≫ tateBondingMap R A B b h = α.hom ≫ b X g :=
    tateBondingMap_comp R A B b h X g
  rw [hg, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.MotivicHomotopy
