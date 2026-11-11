/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholeFibers
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Whole retained supports after changing the first source

The map changes the first factor of the actual relative product and leaves the
second factor unchanged. The associated square is proved Cartesian. Comapping
an ideal through this map gives the whole Cartesian pullback of its support over
the first source, with both original projections. These statements retain all
nilpotents and require neither integral components nor nonempty support.

This is the native whole-ideal replacement for the source-square part of
`Motivic/AlgebraicGeometry/Correspondences/Moving/Pencils/SignedSourceEndpoints.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `81844c665922764c96de0dd51260c8e7d06c85c5`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

open PolynomialSectionPencil

variable {S X X' Y : Scheme.{u}} (q : X ⟶ S) (q' : X' ⟶ S) (r : Y ⟶ S)
  (f : X' ⟶ X) (hf : f ≫ q = q')

/-- Change only the first source of the actual relative product. -/
def retainedSourceChange : pullback q' r ⟶ pullback q r :=
  pullback.lift (pullback.fst q' r ≫ f) (pullback.snd q' r) (by
    rw [Category.assoc, hf, pullback.condition])

@[reassoc (attr := simp)]
theorem retainedSourceChange_fst :
    retainedSourceChange q q' r f hf ≫ pullback.fst q r = pullback.fst q' r ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem retainedSourceChange_snd :
    retainedSourceChange q q' r f hf ≫ pullback.snd q r = pullback.snd q' r :=
  pullback.lift_snd _ _ _

/-- The unchanged second factor makes the first-source square Cartesian. -/
theorem retainedSourceChange_isPullback :
    IsPullback (retainedSourceChange q q' r f hf) (pullback.fst q' r)
      (pullback.fst q r) f where
  w := retainedSourceChange_fst q q' r f hf
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s ↦ by
    have hc : s.snd ≫ q' = (s.fst ≫ pullback.snd q r) ≫ r := by
      rw [← hf, ← Category.assoc, ← s.condition]
      simp only [Category.assoc, pullback.condition]
    refine ⟨pullback.lift s.snd (s.fst ≫ pullback.snd q r) hc, ?_, ?_, ?_⟩
    · change pullback.lift s.snd (s.fst ≫ pullback.snd q r) hc ≫
        retainedSourceChange q q' r f hf = s.fst
      apply pullback.hom_ext (f := q) (g := r)
      · simp only [Category.assoc, retainedSourceChange_fst, pullback.lift_fst_assoc]
        exact s.condition.symm
      · simp only [Category.assoc, retainedSourceChange_snd, pullback.lift_snd]
    · exact pullback.lift_fst _ _ _
    · intro l hl₁ hl₂
      change (l : s.pt ⟶ pullback q' r) = _
      change l ≫ retainedSourceChange q q' r f hf = s.fst at hl₁
      change l ≫ pullback.fst q' r = s.snd at hl₂
      apply pullback.hom_ext (f := q') (g := r)
      · simpa only [pullback.lift_fst] using hl₂
      · have ht := congrArg (fun a ↦ a ≫ pullback.snd q r) hl₁
        simpa only [Category.assoc, retainedSourceChange_snd,
          pullback.lift_snd] using ht)⟩

variable (I : (pullback q r).IdealSheafData)

local notation "g" => retainedSourceChange q q' r f hf
local notation "J" => I.comap g

/-- The entire pulled-back support is the actual first-source fiber product. -/
def retainedSupportPullbackIso :
    pullback f (I.subschemeι ≫ pullback.fst q r) ≅ (J).subscheme :=
  wholeFiberIso g (pullback.fst q' r) (pullback.fst q r) f
    (retainedSourceChange_isPullback q q' r f hf) I.subschemeι ≪≫
      (I.comapIso g).symm

/-- The comparison preserves the literal first-source map. -/
@[reassoc]
theorem retainedSupportPullbackIso_hom_source :
    (retainedSupportPullbackIso q q' r f hf I).hom ≫
        (J).subschemeι ≫ pullback.fst q' r =
      pullback.fst f (I.subschemeι ≫ pullback.fst q r) := by
  simp only [retainedSupportPullbackIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    IdealSheafData.comapIso_inv_subschemeι_assoc, wholeFiberIso_hom_base]

/-- The comparison also preserves the unchanged original target map. -/
@[reassoc]
theorem retainedSupportPullbackIso_hom_target :
    (retainedSupportPullbackIso q q' r f hf I).hom ≫
        (J).subschemeι ≫ pullback.snd q' r =
      pullback.snd f (I.subschemeι ≫ pullback.fst q r) ≫
        I.subschemeι ≫ pullback.snd q r := by
  simp only [retainedSupportPullbackIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    IdealSheafData.comapIso_inv_subschemeι_assoc]
  let e := wholeFiberIso g (pullback.fst q' r) (pullback.fst q r) f
    (retainedSourceChange_isPullback q q' r f hf) I.subschemeι
  change e.hom ≫ pullback.fst g I.subschemeι ≫ pullback.snd q' r = _
  calc
    _ = e.hom ≫ (pullback.fst g I.subschemeι ≫ g) ≫ pullback.snd q r := by
      simp only [Category.assoc, retainedSourceChange_snd]
    _ = e.hom ≫ (pullback.snd g I.subschemeι ≫ I.subschemeι) ≫ pullback.snd q r := by
      rw [pullback.condition]
    _ = _ := by
      simp only [e, Category.assoc, wholeFiberIso_hom_total_assoc]

/-- The inverse comparison expresses the new finite-flat projection as an
isomorphism followed by the ordinary base change of the old projection. -/
@[reassoc]
theorem retainedSupportPullbackIso_inv_source :
    (retainedSupportPullbackIso q q' r f hf I).inv ≫
      pullback.fst f (I.subschemeι ≫ pullback.fst q r) =
        (J).subschemeι ≫ pullback.fst q' r := by
  rw [← retainedSupportPullbackIso_hom_source q q' r f hf I,
    Iso.inv_hom_id_assoc]

/-- Whole finite support stays finite under the actual source change. -/
theorem retainedSupportSource_isFinite [IsFinite (I.subschemeι ≫ pullback.fst q r)] :
    IsFinite ((J).subschemeι ≫ pullback.fst q' r) := by
  rw [← retainedSupportPullbackIso_inv_source q q' r f hf I]
  infer_instance

/-- Flatness is transported for the whole support, not its integral components. -/
theorem retainedSupportSource_flat [Flat (I.subschemeι ≫ pullback.fst q r)] :
    Flat ((J).subschemeι ≫ pullback.fst q' r) := by
  rw [← retainedSupportPullbackIso_inv_source q q' r f hf I]
  infer_instance

end AlgebraicGeometry.Scheme.RelativeCurvePencil
