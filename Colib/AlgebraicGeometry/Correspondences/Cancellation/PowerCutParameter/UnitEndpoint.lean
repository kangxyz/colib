/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.GraphExterior
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry

/-!
# The unit of the native torus as an affine endpoint

The forward Laurent chart identifies the torus unit with polynomial
evaluation at one. The unit section over any smooth source is therefore
the literal Cartesian endpoint of the flat affine-line coordinate map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction AffineLineFiber
open NativeTorusPolynomial

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "T" => multiplicativeGroupObject Sₖ

/-- The affine-line map of the original positive torus coordinate. -/
def torusPowerParameterAffineLine : (T).left ⟶ Spec (.of (Polynomial k)) :=
  (torusFieldChart (k := k)).inv ≫ Spec.map (CommRingCat.ofHom Polynomial.toLaurent)

instance torusPowerParameterAffineLine_isOpenImmersion :
    IsOpenImmersion (torusPowerParameterAffineLine k) := by
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Polynomial.toLaurent : Polynomial k →+* LaurentPolynomial k))) :=
    IsOpenImmersion.of_isLocalization (Polynomial.X : Polynomial k)
  unfold torusPowerParameterAffineLine
  infer_instance

private theorem torusOne_eq_affineLaurentPoint :
    (torusOne Sₖ).left =
      Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id k) (1 : kˣ))) ≫
        (torusFieldChart (k := k)).hom := by
  let e := LaurentPolynomial.eval₂ (RingHom.id k) (1 : kˣ)
  let b : Spec (.of (LaurentPolynomial k)) ⟶ Sₖ := chartProjection ≫ 𝟙 Sₖ
  have hb : Spec.map (CommRingCat.ofHom e) ≫ b = 𝟙 Sₖ := by
    dsimp only [b]
    rw [Category.comp_id, chartProjection, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact LaurentPolynomial.eval₂_C (RingHom.id k) (1 : kˣ) a
  have hu : Units.map e.toMonoidHom chartUnit = 1 := by
    apply Units.ext
    simp [e, chartUnit_val]
  have hc : (torusFieldChart (k := k)).hom = (nativeAffineTorusPoint b chartUnit).left :=
    chartMap_snd (𝟙 Sₖ)
  symm
  rw [hc, ← nativeAffineTorusPoint_natural b e chartUnit, hb, hu]
  change (nativeTorusPoint (𝟙 Sₖ) (specGlobalUnit (1 : kˣ))).left =
    (nativeTorusPoint (𝟙 Sₖ) 1).left
  simp [specGlobalUnit]

/-- The torus unit is the rational point one on the actual affine line. -/
@[reassoc]
theorem torusOne_affineLine :
    (torusOne Sₖ).left ≫ torusPowerParameterAffineLine k = point (1 : k) := by
  rw [torusOne_eq_affineLaurentPoint, torusPowerParameterAffineLine, Category.assoc,
    Iso.hom_inv_id_assoc, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro a
    simp
  · simp

/-- The unit is the exact fibre over one, since the positive torus is open. -/
theorem torusOne_affineLine_isPullback :
    IsPullback (torusOne Sₖ).left (𝟙 Sₖ) (torusPowerParameterAffineLine k) (point (1 : k)) := by
  let e : Sₖ ⟶ (T).left := (torusOne Sₖ).left
  let p : Sₖ ⟶ Spec (.of (Polynomial k)) := point (1 : k)
  change IsPullback e (𝟙 Sₖ) (torusPowerParameterAffineLine k) p
  let : IsIso (𝟙 Sₖ) := (Iso.refl Sₖ).isIso_hom
  apply IsPullback.of_vert_isIso_mono
  exact ⟨(torusOne_affineLine k).trans (Category.id_comp p).symm⟩

variable (X : SmoothSite (Spec (.of k)))

/-- The original torus coordinate of a smooth source, viewed in the affine line. -/
abbrev torusPowerSourceAffineLine : (product X T).left ⟶ Spec (.of (Polynomial k)) :=
  pullback.snd X.hom (T).hom ≫ torusPowerParameterAffineLine k

instance torusPowerSourceAffineLine_flat : Flat (torusPowerSourceAffineLine k X) := by
  let : Flat (pullback.snd X.hom (T).hom) :=
    Flat.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback X.hom (T).hom)
      (inferInstance : Flat X.hom)
  infer_instance

/-- The native unit section is the Cartesian affine endpoint over one. -/
theorem torusUnitSection_affineLine_isPullback :
    IsPullback (unitSection.app X).left X.hom (torusPowerSourceAffineLine k X) (point (1 : k)) := by
  let e := (unitSection.app X).left
  let u := (torusOne Sₖ).left
  have he : e ≫ pullback.fst X.hom (T).hom = 𝟙 _ :=
    congrArg (fun m => m.left) (unitSection_projection X)
  have hcomm : e ≫ pullback.snd X.hom (T).hom = X.hom ≫ u :=
    congrArg (fun m => m.left) (productLift_snd (𝟙 X) (toBase X ≫ torusOne Sₖ))
  have hu : u ≫ (T).hom = 𝟙 Sₖ := MorphismProperty.Over.w (torusOne Sₖ)
  have H : IsPullback (e ≫ pullback.fst X.hom (T).hom) X.hom X.hom (u ≫ (T).hom) := by
    rw [he, hu]
    exact IsPullback.of_id_fst
  have H' := H.of_right hcomm (IsPullback.of_hasPullback X.hom (T).hom)
  let s : X.left ⟶ Sₖ := X.hom
  have H'' : IsPullback e (s ≫ 𝟙 Sₖ) (torusPowerSourceAffineLine k X) (point (1 : k)) :=
    H'.paste_vert (torusOne_affineLine_isPullback k)
  change IsPullback e s (torusPowerSourceAffineLine k X) (point (1 : k))
  exact Eq.mp (congrArg
    (fun t : X.left ⟶ Sₖ => IsPullback e t (torusPowerSourceAffineLine k X) (point (1 : k)))
    (Category.comp_id s)) H''

end AlgebraicGeometry.Cor
