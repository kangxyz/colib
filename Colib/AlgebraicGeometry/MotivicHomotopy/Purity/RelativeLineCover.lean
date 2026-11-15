/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.TransferExcision
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry

/-! # Transfer pushout for the original affine and Laurent opens -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]

local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))
variable {U X W : SmoothSite (Spec (CommRingCat.of k))} (j : U ⟶ X)
  (i : affineLineCylinder.obj U ⟶ W) (l : torusCylinder.obj X ⟶ W)
  (v : W ⟶ affineLineCylinder.obj X) [IsOpenImmersion v.left]
  (hi : i ≫ v = affineLineCylinder.map j) (hl : l ≫ v = openInclusion.app X)

/-- The equivariant comparison of the nested first term with the literal
relative Laurent pair. Its map is the original open-cover excision map. -/
def relativeLineOpenCoverSquare : Square Sm where
  f₁₂ := openInclusion.app U
  f₁₃ := torusCylinder.map j
  f₂₄ := i
  f₃₄ := l
  fac := by
    have : Mono v := (SmoothSite.forgetScheme (Spec (CommRingCat.of k))).mono_of_mono_map
      (inferInstanceAs (Mono v.left))
    apply (cancel_mono v).1
    rw [Category.assoc, Category.assoc, hi, hl]
    exact (openInclusion.naturality j).symm

/-- The original map from the Laurent intersection pair to the first chart. -/
abbrev relativeLineLaurentArrow :
    Arrow.mk (torusCylinder.map j) ⟶ Arrow.mk i :=
  let sq := relativeLineOpenCoverSquare k j i l v hi hl
  Arrow.homMk' sq.f₁₂ sq.f₃₄ sq.fac

variable [IsOpenImmersion i.left] [IsOpenImmersion l.left]

/-- The original open-cover square becomes a pushout of transfer representables. -/
theorem relativeLineTransferPushout
    (hpull : (relativeLineOpenCoverSquare k j i l v hi hl).IsPullback)
    (hunion : Set.range i.left ∪ Set.range l.left = Set.univ) :
    let sq := relativeLineOpenCoverSquare k j i l v hi hl
    let R := smoothTransferRepresentable k
    IsPushout (R.map (torusCylinder.map j)) (R.map sq.f₁₂)
      (R.map sq.f₃₄) (R.map i) := by
  intro sq R
  let : IsOpenImmersion sq.f₂₄.left := inferInstanceAs (IsOpenImmersion i.left)
  let : IsOpenImmersion sq.f₃₄.left := inferInstanceAs (IsOpenImmersion l.left)
  exact (transferSquare_isPushout_of_openCover k sq hpull hunion).flip

end AlgebraicGeometry.MotivicHomotopy
