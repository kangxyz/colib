/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.AmbientParameterQuotient
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Smoothness and the exact ideal of the ambient parameter pair

The original exterior ambient maps smoothly to `T ×[k] T`: first forget
its two outside coordinates, then forget both original middle coordinates.
Both steps are native pullback maps of smooth projections. The parameter
quotient has precisely the inverse-image ideal of the diagonal, without
radicalization. No assertion about correspondence supports is used here.

Native suppliers are Mathlib's `MorphismProperty.pullbackMap`, smooth
composition and `Scheme.IdealSheafData.ker_fst_of_isClosedImmersion`.
The exact pinned source locations are recorded in the companion source report.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u
namespace Stacks.Chow

/-- The actual middle-pair projection is smooth when both outside factors are smooth. -/
instance smooth_correspondenceMiddlePair {S X Y Z : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) [Smooth f] [Smooth h] :
    Smooth (correspondenceMiddlePair f g h) := by
  unfold correspondenceMiddlePair
  exact MorphismProperty.pullbackMap (P := @Smooth)
    (inferInstanceAs (Smooth (pullback.snd f g)))
    (inferInstanceAs (Smooth (pullback.fst g h))) rfl rfl

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))

/-- Forgetting all but the two actual parameter coordinates is smooth. -/
instance exteriorAmbientParameterPair_smooth :
    Smooth (exteriorAmbientParameterPair X Y Z T) := by
  unfold exteriorAmbientParameterPair
  apply MorphismProperty.comp_mem (@Smooth)
  · infer_instance
  · exact MorphismProperty.pullbackMap (P := @Smooth)
      (inferInstanceAs (Smooth (pullback.snd Y.hom T.hom)))
      (inferInstanceAs (Smooth (pullback.snd Y.hom T.hom)))
      (by simp only [SmoothSite.product_hom, pullback.condition])
      (by simp only [SmoothSite.product_hom, pullback.condition])

/-- The original ambient parameter quotient is cut out by the actual diagonal ideal. -/
theorem exteriorAmbientParameterInclusion_ker :
    (exteriorAmbientParameterInclusion X Y Z T).ker =
      (pullback.diagonal T.hom).ker.comap (exteriorAmbientParameterPair X Y Z T) := by
  calc
    (exteriorAmbientParameterInclusion X Y Z T).ker =
        ((pullbackSymmetry (exteriorAmbientParameterPair X Y Z T)
          (pullback.diagonal T.hom)).hom ≫
            exteriorAmbientParameterInclusion X Y Z T).ker :=
      (Scheme.Hom.ker_comp_of_isIso _ _).symm
    _ = (pullback.fst (exteriorAmbientParameterPair X Y Z T)
        (pullback.diagonal T.hom)).ker := by simp
    _ = (pullback.diagonal T.hom).ker.comap (exteriorAmbientParameterPair X Y Z T) :=
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _

end Stacks.Chow
