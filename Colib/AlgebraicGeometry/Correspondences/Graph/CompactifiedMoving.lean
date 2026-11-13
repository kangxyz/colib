/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedMoving
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.CompactifiedMoving

/-!
# Moving correspondences on a compactified relative curve

The geometric graph pencil gives a finite correspondence on the actual
affine-line cylinder. The second endpoint factors through the good open
and the first is the original graph after cancelling the constant pole.

Adapted from `Motivic/AlgebraicGeometry/Correspondences/Moving/OneSided/LocalMoving.lean`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Stacks.Ample

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.RelativeCurvePencil

variable {k R : Type u} [Field k] [CommRing R] [IsNoetherianRing R]
  {C Y D Z : Scheme.{u}}
  (π : C ⟶ Spec (.of R)) [IsProper π]
  (j : Y ⟶ C) [IsOpenImmersion j] [IsAffine Y] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (t : Spec (.of R) ⟶ Spec (.of k))
  [Smooth ((j ≫ π) ≫ t)] [IsSeparated ((j ≫ π) ≫ t)] [QuasiCompact ((j ≫ π) ≫ t)]
  {A : SmoothSite (Spec (.of k))}
  (a : A ⟶ SmoothSite.mk ((j ≫ π) ≫ t)) [IsOpenImmersion a.left]
  (s : Z ⟶ Y) [IsClosedImmersion (s ≫ j)] [IsFinite (s ≫ j ≫ π)]
  (d : D ⟶ C) [IsClosedImmersion d] [IsFinite (d ≫ π)]
  (hd : Disjoint (Set.range j) (Set.range d))
  (hY : ∀ c : C, c ∈ Set.range j ∨ c ∈ Set.range d)
  (hA : ∀ c : C, c ∈ Set.range (a.left ≫ j) ∨
    c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
  (M : C.Modules) [IsInvertibleModule C M] (hM : IsAmple C M)

local notation "r" => j ≫ π
local notation "W" => SmoothSite.mk (r ≫ t)

include hd hY hA hM in
/-- A proper relative curve presentation gives actual moving endpoints around
each point of its original retained target. -/
theorem exists_affine_open_hasMovingEndpoints (x : Y) :
    ∃ O : Y.affineOpens, x ∈ O.1 ∧
      let : IsAffine O.1.toScheme := O.2
      let : IsAffineHom O.1.ι := isAffineHom_of_isAffine O.1.ι
      HasMovingEndpoints (k := k)
        (SmoothSite.homMk (X := SmoothSite.mk (O.1.ι ≫ (W).hom)) (Y := W) O.1.ι rfl) a := by
  obtain ⟨O, hx, ⟨P⟩⟩ :=
    exists_affine_open_retainedGraphPencil (k := k) π j t a.left s d hd hY hA M hM x
  let u := O.1.ι
  let q := u ≫ r
  let : IsAffine O.1.toScheme := O.2
  let : IsAffineHom u := isAffineHom_of_isAffine u
  let : IsAffineHom t := isAffineHom_of_isAffine t
  let : Smooth (q ≫ t) := by
    change Smooth ((u ≫ r) ≫ t)
    rw [Category.assoc]
    infer_instance
  let : IsSeparated (q ≫ t) := by
    change IsSeparated ((u ≫ r) ≫ t)
    rw [Category.assoc]
    infer_instance
  let : QuasiCompact (q ≫ t) := by
    change QuasiCompact ((u ≫ r) ≫ t)
    rw [Category.assoc]
    infer_instance
  let := P.line_invertible
  let := P.poleLine_invertible
  let := P.family_finite
  let := P.family_flat
  let family := nativeRetainedFamilySource (k := k) t q r P.line P.graphPole P.numerator
  let familyFinite : IsFinite family := by
    dsimp only [family]
    unfold nativeRetainedFamilySource
    infer_instance
  let familyFlat : Flat family := by
    dsimp only [family]
    unfold nativeRetainedFamilySource
    infer_instance
  let witnesses : RetainedPencilWitnesses (k := k) t q r P.line P.poleLine
      P.graphPole P.numerator P.pole :=
    ⟨familyFinite, familyFlat, P.pole_finite, P.pole_relativeCartier.2⟩
  exact ⟨O, hx, hasMovingEndpoints_of_retainedPencil (k := k) t q r u rfl P.line P.poleLine
    P.graphPole P.numerator P.pole witnesses a P.pole_relativeCartier.1 P.graphPole_zero
    P.numerator_support P.pole_support⟩

end AlgebraicGeometry.Cor
