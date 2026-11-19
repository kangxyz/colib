/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Approximation.WeakImage
public import Colib.KTheory.Waldhausen.Approximation.GeneralKEquivalence

/-! # Original approximation onto the actual witnessed weak image

The actual inherited target structure is constructed from restricted lifting.
The original corestriction then satisfies genuine App1/App2. Approximation
identifies its K-groups with those of the source, while the target inclusion
retains exactly the original functor's K-map and its actual image. No
cofinality or injectivity claim is made for that inclusion.

Implementation provenance: `Quillen/Waldhausen/Approximation/WeakImageKEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

noncomputable section
open CategoryTheory Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.ApproximationImage
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationOnImage W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  [V.weq.HasTwoOutOfThreeProperty]
  (J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W))

include J in
/-- The actual corestriction S-map is a complete weak equivalence. -/
theorem corestrict_deloopingMap_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (deloopingMap (corestrict_exact h hF)).hom :=
  (corestrict_approximation h hF).deloopingMap_isWeakHomotopyEquivalence_general
    (corestrict_exact h hF) J

include J in
/-- The original corestriction K-map is bijective, without any all-target App2 hypothesis. -/
theorem corestrict_KMap_bijective (n : ℕ) : Function.Bijective (KMap (corestrict_exact h hF) n) :=
  (corestrict_approximation h hF).KMap_bijective_general (corestrict_exact h hF) J n

/-- Approximation onto the witnessed image, with the original corestriction forward. -/
def corestrictKEquiv (n : ℕ) : W.K n ≃* (waldhausenStructure h hF).K n :=
  MulEquiv.ofBijective (KMap (corestrict_exact h hF) n) (corestrict_KMap_bijective h hF J n)

/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem corestrictKEquiv_coe (n : ℕ) :
    (↑(corestrictKEquiv h hF J n) : W.K n →* (waldhausenStructure h hF).K n) = KMap
        (corestrict_exact h hF) n := rfl

omit [V.weq.HasTwoOutOfThreeProperty] in
/-- The actual original canonical K-map factors through the literal image inclusion. -/
theorem inclusion_KMap_comp_corestrict (n : ℕ) :
    (KMap (inclusion_exact h hF) n).comp (KMap (corestrict_exact h hF) n) = KMap hF n := by
  rw [KMap_comp_KMap]

include J in
/-- The image-inclusion map has exactly the image of the actual original K-map,
in all degrees. Its injectivity or higher cofinality is not an input or conclusion. -/
theorem range_inclusion_KMap (n : ℕ) :
    (KMap (inclusion_exact h hF) n).range = (KMap hF n).range := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := (corestrict_KMap_bijective h hF J n).surjective a
    exact ⟨b, (DFunLike.congr_fun (inclusion_KMap_comp_corestrict h hF n) b).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨KMap (corestrict_exact h hF) n a,
      DFunLike.congr_fun (inclusion_KMap_comp_corestrict h hF n) a⟩

end CategoryTheory.Waldhausen.ApproximationImage

attribute [colib_tag "COL-1316",
  colib_ref "quillen" "Quillen/Waldhausen/Approximation/WeakImageKEquivalence.lean:36-73"
    "adaptation" "Canonical approximation of the witnessed image and factorization of the K-map"]
  CategoryTheory.Waldhausen.ApproximationImage.corestrictKEquiv
  CategoryTheory.Waldhausen.ApproximationImage.inclusion_KMap_comp_corestrict
