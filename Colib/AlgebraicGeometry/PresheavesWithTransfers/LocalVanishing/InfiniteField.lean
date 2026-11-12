/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.AffineClosedPoint
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.Presentation.OriginalOpen
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.InfiniteOriginalEtalePresentation

/-!
# Integral-affine local vanishing over an infinite field

On the original smooth affine spectrum, the actual bad closed subscheme
and the good affine open give an original étale presentation at each
closed point of positive dimension. The transfer action supplies a zero
neighborhood in that same affine spectrum.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

/-- The actual infinite-field presentations imply integral-affine local zero. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/A1/LocalVanishing/Affine/IntegralDetection.lean:24-59"
  "adaptation" "Local zero on the original affine neighborhood over an infinite field"]
theorem integralAffineLocalZero_of_infinite (k : Type u) [Field k] [Infinite k] :
    IntegralAffineLocalZero k := by
  apply integralAffineLocalZero_of_affineClosedPoint
  intro B _ _ _ _ x _ J hJ d hd A _ a _ ha hcover P hP s hs
  let : IsAffine (SmoothSite.affineSite k B).left :=
    inferInstanceAs (IsAffine (Spec (.of B)))
  let z := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have : IsClosedImmersion z :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have H : IsPullback z (𝟙 _) (𝟙 _) z := IsPullback.of_vert_isIso ⟨by simp⟩
  obtain ⟨e⟩ :=
    QuadraticIncidence.InfinityChart.nonempty_originalEtalePresentation
      k B x J hJ d hd (𝟙 _) a.left z (by simp only [Category.comp_id]; rfl) H ha hcover
  exact RelativeCurve.OriginalEtalePresentation.exists_zero_on_original_open
    (𝟙 _) a z z x e P hP s hs

end AlgebraicGeometry.PresheafWithTransfers
