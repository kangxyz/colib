/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.AffineLine.Open.OriginalRefinement
public import Colib.AlgebraicGeometry.Sites.Smooth.AffineLine.CylinderNativeCoordinates

/-!
# Polynomial coordinates for the original distinguished representatives

The affine coefficient restriction is a Cartesian restriction of the whole
cylinder. The two given representatives retain their actual maps to the
original distinguished cover after this restriction.

Adapted from `Motivic/Cohomology/A1/Sheafification/WholeCylinderLifting.lean`
at a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.PolynomialLaurent AlgebraicGeometry.Scheme.SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates

variable {k : Type u} [Field k] (U T : SmoothSite (Spec (.of k))) [IsAffine U.left]
  (e : T ≅ affineLineCylinder.obj U) (O : (Spec Γ(U.left, ⊤)).Opens) [IsAffine O.toScheme]

local notation "proj" => projection (SmoothSite.additiveGroupObject (Spec (.of k)))
local notation "q₀" => (e.hom.left ≫ ((proj).app U).left ≫ U.left.isoSpec.hom)
local notation "qN" => polynomialProjection (.of Γ(O.toScheme, ⊤))
local notation "c₀" => (O.toScheme.isoSpec.inv ≫ O.ι)
local notation "E₀" => originalAffineRefinedTargetIso Γ(U.left, ⊤)
  (originalCylinderNativeIso U T e) q₀ (originalCylinderNativeIso_projection U T e) O

/-- The exact Cartesian cylinder and the two representative restrictions over
the given affine coefficient open. -/
theorem exists_polynomialRepresentativeRefinement
    {A Y : Scheme.{u}} (a : A ⟶ T.left) (p : Y ⟶ T.left)
    (W : Y.Opens) (hW : W ≤ p ⁻¹ᵁ (q₀ ⁻¹ᵁ O))
    (t : Spec Γ(O.toScheme, ⊤) ⟶ Spec (.of k)) [Smooth t]
    (ht : t = c₀ ≫ U.left.isoSpec.inv ≫ U.hom)
    [Smooth (polynomialProjection (.of Γ(O.toScheme, ⊤)))] :
    ∃ (l : SmoothSite.mk t ⟶ U) (m : SmoothSite.mk (qN ≫ t) ⟶ T),
      IsOpenImmersion l.left ∧
      IsPullback (m ≫ e.hom).left qN ((proj).app U).left l.left ∧
      l.left = c₀ ≫ U.left.isoSpec.inv ∧ m.left = (E₀).inv ≫ (q₀ ⁻¹ᵁ O).ι ∧
      ((a ≫ q₀) ⁻¹ᵁ O).ι ≫ a =
        originalAffineRefinedNativePuncture Γ(U.left, ⊤) (originalCylinderNativeIso U T e)
          q₀ (originalCylinderNativeIso_projection U T e) O a ≫ m.left ∧
      W.ι ≫ p =
        originalAffineRefinedNativeMap Γ(U.left, ⊤) (originalCylinderNativeIso U T e)
          q₀ (originalCylinderNativeIso_projection U T e) O p W hW ≫ m.left := by
  let lS := c₀ ≫ U.left.isoSpec.inv
  let mS := (E₀).inv ≫ (q₀ ⁻¹ᵁ O).ι
  have Hnative : IsPullback mS qN q₀ c₀ :=
    originalAffineRefinedTarget_isPullback Γ(U.left, ⊤) (originalCylinderNativeIso U T e)
      q₀ (originalCylinderNativeIso_projection U T e) O
  let l : SmoothSite.mk t ⟶ U := SmoothSite.homMk lS
    ((Category.assoc c₀ U.left.isoSpec.inv U.hom).trans ht.symm)
  have hT : q₀ ≫ U.left.isoSpec.inv ≫ U.hom = T.hom := by
    calc
      _ = e.hom.left ≫ ((proj).app U).left ≫ U.hom := by
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = e.hom.left ≫ (affineLineCylinder.obj U).hom :=
        congrArg (fun f ↦ e.hom.left ≫ f) (MorphismProperty.Over.w ((proj).app U))
      _ = _ := MorphismProperty.Over.w e.hom
  let m : SmoothSite.mk (qN ≫ t) ⟶ T := SmoothSite.homMk mS (by
    change mS ≫ T.hom = qN ≫ t
    calc
      _ = mS ≫ q₀ ≫ U.left.isoSpec.inv ≫ U.hom := congrArg (fun f ↦ mS ≫ f) hT.symm
      _ = (mS ≫ q₀) ≫ U.left.isoSpec.inv ≫ U.hom := (Category.assoc _ _ _).symm
      _ = (qN ≫ c₀) ≫ U.left.isoSpec.inv ≫ U.hom :=
        congrArg (fun f ↦ f ≫ U.left.isoSpec.inv ≫ U.hom) Hnative.w
      _ = qN ≫ t := (Category.assoc _ _ _).trans (congrArg (fun f ↦ qN ≫ f) ht.symm))
  have Horiginal : IsPullback e.hom.left q₀ ((proj).app U).left U.left.isoSpec.inv := by
    apply IsPullback.of_horiz_isIso
    constructor
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨l, m, ?_, Hnative.paste_horiz Horiginal, rfl, rfl, ?_, ?_⟩
  · change IsOpenImmersion ((O.toScheme.isoSpec.inv ≫ O.ι) ≫ U.left.isoSpec.inv)
    infer_instance
  · change (a ⁻¹ᵁ (q₀ ⁻¹ᵁ O)).ι ≫ a = _ ≫ mS
    simpa only [originalAffineRefinedNativePuncture, mS, Category.assoc,
      Iso.hom_inv_id_assoc] using (morphismRestrict_ι a (q₀ ⁻¹ᵁ O)).symm
  · change _ = _ ≫ mS
    simpa only [originalAffineRefinedNativeMap, mS, Category.assoc,
      Iso.hom_inv_id_assoc] using (Hom.resLE_comp_ι p hW).symm

end AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
