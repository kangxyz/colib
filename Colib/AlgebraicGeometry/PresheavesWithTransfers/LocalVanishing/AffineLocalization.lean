/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.GenericOpen
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.Coordinates
public import Colib.RingTheory.Smooth.Localization

/-!
# Generic open zeros from affine localizations

The canonical affine coordinates turn localization away from a nonzero
element into an original affine open containing the generic point.

Adapted from `Motivic/Cohomology/A1/LocalVanishing/Presheaf/AffineModelGenericZero.lean`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `e04854c69a0d3b13c9c14e71c18c2a38c1b4173d`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open _root_.Algebra.Smooth

attribute [local instance] away_smooth

variable {k : Type u} [Field k]

/-- A zero witness on each smooth affine domain is an actual principal localization. -/
def AffineLocalizationZero (P : PresheafWithTransfers.{v} k) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (s : sections P (Cor.mk (affineSite k R))),
    ∃ r : R, r ≠ 0 ∧ transfer P ((Cor.graphFunctor k).map
      (affineMorphism (IsScalarTower.toAlgHom k R (Localization.Away r)))) s = 0

/-- Affine localization witnesses give genuine original generic open zeros. -/
theorem hasGenericOpenZeros_of_affineLocalizationZero
    (P : PresheafWithTransfers.{v} k) (hP : P.AffineLocalizationZero) :
    P.HasGenericOpenZeros := by
  intro X _ _ s
  let R := Γ(X.left, ⊤)
  let : Algebra k R := AffineSectionCoordinates.sectionsAlgebra X
  let : Algebra.Smooth k R := AffineSectionCoordinates.sectionsSmooth X
  let e := AffineSectionCoordinates.affineIso X
  obtain ⟨r, hr, hz⟩ := hP R (transfer P ((Cor.graphFunctor k).map e.hom) s)
  let : IsDomain (Localization.Away r) := Localization.Away.isDomain hr
  let : IsIntegral (affineSite k (Localization.Away r)).left :=
    inferInstanceAs (IsIntegral (Spec (.of (Localization.Away r))))
  let a : affineSite k (Localization.Away r) ⟶ X :=
    affineMorphism (IsScalarTower.toAlgHom k R (Localization.Away r)) ≫ e.hom
  let : IsAffine (affineSite k (Localization.Away r)).left :=
    inferInstanceAs (IsAffine (Spec (.of (Localization.Away r))))
  let : IsOpenImmersion a.left := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization.Away r))) ≫ X.left.isoSpec.inv)
    infer_instance
  have ha : transfer P ((Cor.graphFunctor k).map a) s = 0 := by
    rw [show a = affineMorphism (IsScalarTower.toAlgHom k R (Localization.Away r)) ≫ e.hom
      from rfl, Functor.map_comp, transfer_comp]
    exact hz
  exact ⟨a.left.opensRange,
    ⟨genericPoint (Spec (.of (Localization.Away r))), genericPoint_eq_of_isOpenImmersion a.left⟩,
    P.zero_on_open_image_general a s ha⟩

end AlgebraicGeometry.PresheafWithTransfers
