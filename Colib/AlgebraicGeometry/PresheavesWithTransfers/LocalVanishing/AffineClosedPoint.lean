/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.IntegralAffine
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.ZeroDimensional
public import Colib.AlgebraicGeometry.IdealSheaf.Complement.AffineOpenComplementIdeal
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.Coordinates
public import Colib.Topology.JacobsonOpenCover

/-!
# Closed-point detection for integral-affine local vanishing

Positive-dimensional closed-point neighborhoods combine with the
zero-dimensional case and the Jacobson property to give local-zero
neighborhoods at all points. The affine-coordinate comparison carries
the resulting restriction maps back to the original smooth scheme.

Adapted from Motivic at a6805c4a87cdfd7717dd7a94039246a167f15380,
Motivic/Cohomology/A1/LocalVanishing/Original/AffineDetection.lean and
Motivic/Cohomology/A1/LocalVanishing/Affine/IntegralDetection.lean.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.SmoothSite

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

/-- Local-zero neighborhoods at closed points of positive-dimensional affine spectra. -/
def AffineClosedPointLocalZero (k : Type u) [Field k] : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B] [Algebra k B] [Algebra.Smooth k B]
    (x : PrimeSpectrum B) [x.asIdeal.IsMaximal] (J : Ideal B) (_ : J ≠ ⊥)
    (d : ℕ) (_ : Algebra.trdeg k B = (d + 1 : ℕ))
    {A : SmoothSite (Spec (.of k))} [IsAffine A.left]
    (a : A ⟶ affineSite k B) [IsOpenImmersion a.left]
    (_ : Disjoint (Set.range a.left)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (_ : ∀ y : Spec (.of B), y ∈ Set.range a.left ∨
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (P : PresheafWithTransfers.{u + 1} k) (_ : P.IsA1Invariant)
    (v : P.sections (Cor.mk (affineSite k B)))
    (_ : P.transfer ((Cor.graphFunctor k).map a) v = 0),
    ∃ O : (affineSite k B).left.Opens, IsAffineOpen O ∧ x ∈ O ∧
      P.transfer ((Cor.graphFunctor k).map
        (homMk (X := mk (O.ι ≫ (affineSite k B).hom))
          (Y := affineSite k B) O.ι rfl)) v = 0

/-- Local zero from a nonempty affine good open, at every original
point. The zero-dimensional and already-good-point cases bypass presentations. -/
private theorem exists_zero_neighborhood_of_nonempty_affine_open
    (k B : Type u) [Field k] (hClosed : AffineClosedPointLocalZero k)
    [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.Smooth k B]
    {A : SmoothSite (Spec (.of k))} [IsAffine A.left] [Nonempty A.left]
    (a : A ⟶ affineSite k B) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk (affineSite k B)))
    (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0) (x : (affineSite k B).left) :
    ∃ O : (affineSite k B).left.Opens, IsAffineOpen O ∧ x ∈ O ∧
      P.transfer ((Cor.graphFunctor k).map
        (homMk (X := mk (O.ι ≫ (affineSite k B).hom))
          (Y := affineSite k B) O.ι rfl)) v = 0 := by
  classical
  let : IsAffine (affineSite k B).left := inferInstanceAs (IsAffine (Spec (.of B)))
  let J := Scheme.openComplementIdeal B a.left.opensRange
  have hJ : J ≠ ⊥ := Scheme.openComplementIdeal_ne_bot B a.left.opensRange
    (Set.range_nonempty a.left)
  have hr : Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) =
      (Set.range a.left)ᶜ := by
    simpa only [Scheme.Hom.coe_opensRange] using
      Scheme.range_openComplementIdeal B a.left.opensRange
  have ha : Disjoint (Set.range a.left)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) := by
    rw [hr]
    exact disjoint_compl_right
  have hcover : ∀ y : Spec (.of B), y ∈ Set.range a.left ∨
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) := by
    intro y
    rw [hr]
    exact Classical.em _
  by_cases hd : Algebra.trdeg k B = 0
  · have hz := section_zero_of_trdeg_zero k B hd J hJ a hcover P v hv
    refine ⟨⊤, isAffineOpen_top _, trivial, ?_⟩
    dsimp only
    erw [hz, map_zero]
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp
    (trdeg_lt_aleph0_of_finiteType (R := k) (S := B))
  cases n with
  | zero => exact (hd (by simpa using hn)).elim
  | succ d =>
    let Z : (affineSite k B).left.Opens → Prop := fun O => IsAffineOpen O ∧
      P.transfer ((Cor.graphFunctor k).map
        (homMk (X := mk (O.ι ≫ (affineSite k B).hom))
          (Y := affineSite k B) O.ι rfl)) v = 0
    have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
    have : JacobsonSpace (affineSite k B).left :=
      LocallyOfFiniteType.jacobsonSpace (Spec.map (CommRingCat.ofHom (algebraMap k B)))
    have htop : (⨆ O : {O : (affineSite k B).left.Opens // Z O}, O.val) = ⊤ := by
      apply TopologicalSpace.Opens.iSup_eq_top_of_closedPoint_neighborhoods
      intro y hy
      by_cases hya : y ∈ Set.range a.left
      · exact ⟨⟨a.left.opensRange, isAffineOpen_opensRange a.left,
          P.zero_on_open_image_general a v hv⟩, hya⟩
      have : y.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hy
      obtain ⟨O, hO, hyO, hz⟩ := hClosed B y J hJ d hn a ha hcover P hP v hv
      exact ⟨⟨O, hO, hz⟩, hyO⟩
    have hx : x ∈ ⨆ O : {O : (affineSite k B).left.Opens // Z O}, O.val := by
      rw [htop]
      trivial
    obtain ⟨O, hxO⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨hO, hz⟩ := O.property
    exact ⟨O.val, hO, hxO, hz⟩

/-- One nonempty affine chart of the good open supplies the zero input. -/
private theorem exists_zero_neighborhood_of_nonempty_open
    (k B : Type u) [Field k] (hClosed : AffineClosedPointLocalZero k)
    [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.Smooth k B]
    {A : SmoothSite (Spec (.of k))} [Nonempty A.left]
    (a : A ⟶ affineSite k B) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk (affineSite k B)))
    (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0) (x : (affineSite k B).left) :
    ∃ O : (affineSite k B).left.Opens, IsAffineOpen O ∧ x ∈ O ∧
      P.transfer ((Cor.graphFunctor k).map
        (homMk (X := mk (O.ι ≫ (affineSite k B).hom))
          (Y := affineSite k B) O.ι rfl)) v = 0 := by
  obtain ⟨y⟩ := ‹Nonempty A.left›
  obtain ⟨i, t, _⟩ := A.left.affineCover.exists_eq y
  let C := mk (A.left.affineCover.f i ≫ A.hom)
  let c : C ⟶ A := homMk (A.left.affineCover.f i) rfl
  have : IsAffine C.left := inferInstanceAs (IsAffine (A.left.affineCover.X i))
  have : Nonempty C.left := ⟨t⟩
  have : IsOpenImmersion (c ≫ a).left :=
    inferInstanceAs (IsOpenImmersion (A.left.affineCover.f i ≫ a.left))
  apply exists_zero_neighborhood_of_nonempty_affine_open k B hClosed (c ≫ a) P hP v ?_ x
  rw [Functor.map_comp, transfer_comp]
  change P.transfer ((Cor.graphFunctor k).map c)
    (P.transfer ((Cor.graphFunctor k).map a) v) = 0
  rw [hv, map_zero]

/-- Affine coordinates transport local-zero neighborhoods back to the original scheme. -/
private theorem exists_zero_neighborhood_of_integral_affine
    {k : Type u} [Field k] (hClosed : AffineClosedPointLocalZero k)
    {X A : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsIntegral X.left]
    [Nonempty A.left] (a : A ⟶ X) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (v : P.sections (Cor.mk X)) (hv : P.transfer ((Cor.graphFunctor k).map a) v = 0)
    (x : X.left) :
    ∃ O : X.left.Opens, IsAffineOpen O ∧ x ∈ O ∧
      P.transfer ((Cor.graphFunctor k).map
        (homMk (X := mk (O.ι ≫ X.hom)) (Y := X) O.ι rfl)) v = 0 := by
  let : Algebra k Γ(X.left, ⊤) := AffineSectionCoordinates.sectionsAlgebra X
  let e : affineSite k Γ(X.left, ⊤) ≅ X := AffineSectionCoordinates.affineIso X
  have : IsOpenImmersion (a ≫ e.inv).left :=
    inferInstanceAs (IsOpenImmersion (a.left ≫ X.left.isoSpec.hom))
  have hv' : P.transfer ((Cor.graphFunctor k).map (a ≫ e.inv))
      (P.transfer ((Cor.graphFunctor k).map e.hom) v) = 0 := by
    have he : (a ≫ e.inv) ≫ e.hom = a := by simp
    have hv' := hv
    rw [← he, Functor.map_comp, transfer_comp] at hv'
    exact hv'
  obtain ⟨O, hO, hx, hz⟩ := exists_zero_neighborhood_of_nonempty_open
    k Γ(X.left, ⊤) hClosed (a ≫ e.inv) P hP (P.transfer ((Cor.graphFunctor k).map e.hom) v)
      hv' (e.inv.left x)
  let : IsAffine O.toScheme := hO
  let S := mk (O.ι ≫ (affineSite k Γ(X.left, ⊤)).hom)
  let j : S ⟶ affineSite k Γ(X.left, ⊤) := homMk O.ι rfl
  let f := j ≫ e.hom
  have : IsAffine S.left := hO
  have : IsOpenImmersion f.left :=
    inferInstanceAs (IsOpenImmersion (O.ι ≫ X.left.isoSpec.inv))
  have hf : P.transfer ((Cor.graphFunctor k).map f) v = 0 := by
    rw [Functor.map_comp, transfer_comp]
    exact hz
  refine ⟨f.left.opensRange, isAffineOpen_opensRange f.left, ?_,
    P.zero_on_open_image_general f v hf⟩
  refine ⟨⟨e.inv.left x, hx⟩, ?_⟩
  exact congrArg (fun f => f.left x) e.inv_hom_id

/-- The closed-point input gives the integral-affine local-zero property. -/
theorem integralAffineLocalZero_of_affineClosedPoint {k : Type u} [Field k]
    (hClosed : AffineClosedPointLocalZero k) : IntegralAffineLocalZero k := by
  intro X A _ _ _ a _ P hP v hv x
  exact exists_zero_neighborhood_of_integral_affine hClosed a P hP v hv x

end AlgebraicGeometry.PresheafWithTransfers
