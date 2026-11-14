/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Modules.ConcentratedHomologyFaithful
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# Lifting a specified comparison between concentrated objects

Source and target concentration is essential. Fullness is
required ONLY of the original abelian-category functor. No global derived
fullness or equality with the specified comparison is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace DerivedCategory
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable [HasDerivedCategory C] [HasDerivedCategory D]

/-- Reconstruct an iso from its given homology iso inside the concentrated category. -/
def isoOfConcentratedHomology (n : ℤ) {X Y : DerivedCategory C}
    [X.IsGE n] [X.IsLE n] [Y.IsGE n] [Y.IsLE n]
    (a : (homologyFunctor C n).obj X ≅ (homologyFunctor C n).obj Y) : X ≅ Y :=
  normalizedConcentratedHomologyIso X n ≪≫
    (singleFunctor C n).mapIso a ≪≫ (normalizedConcentratedHomologyIso Y n).symm

/-- The reconstructed map has the specified homology map, not a choice-dependent one. -/
theorem isoOfConcentratedHomology_homology (n : ℤ) {X Y : DerivedCategory C}
    [X.IsGE n] [X.IsLE n] [Y.IsGE n] [Y.IsLE n]
    (a : (homologyFunctor C n).obj X ≅ (homologyFunctor C n).obj Y) :
    (homologyFunctor C n).map (isoOfConcentratedHomology n a).hom = a.hom := by
  let H := homologyFunctor C n
  let S := singleFunctor C n
  let c := singleFunctorCompHomologyFunctorIso C n
  let eX := normalizedConcentratedHomologyIso X n
  let eY := normalizedConcentratedHomologyIso Y n
  have hY : H.map eY.inv = c.hom.app (H.obj Y) := by
    apply (cancel_epi (H.map eY.hom)).mp
    rw [← H.map_comp, eY.hom_inv_id, H.map_id]
    exact (normalizedConcentratedHomologyIso_homology Y n).symm
  change H.map (eX.hom ≫ S.map a.hom ≫ eY.inv) = a.hom
  simp only [Functor.map_comp, hY]
  have hc := c.hom.naturality a.hom
  change H.map (S.map a.hom) ≫ c.hom.app (H.obj Y) =
    c.hom.app (H.obj X) ≫ a.hom at hc
  rw [hc, ← Category.assoc, normalizedConcentratedHomologyIso_homology, Category.id_comp]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [F.Full] [F.Faithful]
variable (n : ℤ) {X Y : DerivedCategory C}
variable [X.IsGE n] [X.IsLE n] [Y.IsGE n] [Y.IsLE n]

/-- Calibrate the homology lift using the actual specified abelian derived comparison. -/
def liftConcentratedIso (b : F.mapDerivedCategory.obj X ≅ F.mapDerivedCategory.obj Y) : X ≅ Y :=
  isoOfConcentratedHomology n (F.preimageIso
    (((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F n).app X).symm ≪≫
      (homologyFunctor D n).mapIso b ≪≫
      (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F n).app Y))

/-- The lifted map has precisely the specified image on homology after applying F. -/
theorem liftConcentratedIso_map_homology
    (b : F.mapDerivedCategory.obj X ≅ F.mapDerivedCategory.obj Y) :
    (homologyFunctor D n).map (F.mapDerivedCategory.map (liftConcentratedIso F n b).hom) =
      (homologyFunctor D n).map b.hom := by
  rw [StacksDraft.DerivedCategoryHomology.homologyFunctor_map_mapDerivedCategory_map]
  rw [liftConcentratedIso, isoOfConcentratedHomology_homology]
  simp [Functor.preimageIso, Category.assoc]

/-- On concentrated images the reconstructed map equals the specified comparison itself. -/
theorem liftConcentratedIso_map
    [IsGE (F.mapDerivedCategory.obj X) n] [IsLE (F.mapDerivedCategory.obj X) n]
    [IsGE (F.mapDerivedCategory.obj Y) n] [IsLE (F.mapDerivedCategory.obj Y) n]
    (b : F.mapDerivedCategory.obj X ≅ F.mapDerivedCategory.obj Y) :
    F.mapDerivedCategory.map (liftConcentratedIso F n b).hom = b.hom := by
  apply concentrated_hom_eq_of_homology n
  exact liftConcentratedIso_map_homology F n b

end DerivedCategory
