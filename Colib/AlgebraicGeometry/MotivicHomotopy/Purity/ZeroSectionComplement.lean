/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ClosedPair
public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.CylinderComplement
import Colib.AlgebraicGeometry.Sites.Smooth.AffineLine.CylinderRestriction
import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineSectionNaturality

/-! # The actual complement after adjoining a zero coordinate -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.Contraction

variable (R : CommRingCat.{u})
variable [IsNoetherian (Scheme.Spec.obj (Opposite.op R))]

local notation "S(" R ")" => Scheme.Spec.obj (Opposite.op R)
local notation "Sm(" R ")" => SmoothSite (S(R))
local notation "A(" R ")" => SmoothSite.additiveGroupObject (S(R))

variable {Z X : Sm(R)} (z : Z ⟶ X) [IsClosedImmersion z.left]

/-- The composite includes the old support as the last zero coordinate. -/
abbrev appendZeroSection : Z ⟶ affineLineCylinder.obj X :=
  z ≫ nativeAffineSection R X 0

instance appendZeroSection_isClosedImmersion :
    IsClosedImmersion (appendZeroSection R z).left :=
  inferInstanceAs (IsClosedImmersion (z.left ≫ (nativeAffineSection R X 0).left))

omit [IsNoetherian (S(R))] [IsClosedImmersion z.left] in
private theorem range_appendZeroSection :
    Set.range (appendZeroSection R z).left =
      ((projection A(R)).app X).left ⁻¹' Set.range z.left ∩
        Set.range (nativeAffineSection R X 0).left := by
  have hp : (nativeAffineSection R X 0).left ≫ ((projection A(R)).app X).left = 𝟙 X.left :=
    congrArg (fun f => f.left) (nativeAffineSection_projection R X 0)
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨t, by
      change z.left t = (((z.left ≫ (nativeAffineSection R X 0).left) ≫
        ((projection A(R)).app X).left) t)
      rw [Category.assoc, hp, Category.comp_id]
      rfl⟩, ⟨z.left t, rfl⟩⟩
  · rintro ⟨⟨t, ht⟩, ⟨y, rfl⟩⟩
    have hy : z.left t = y := by
      change z.left t = ((nativeAffineSection R X 0).left ≫ ((projection A(R)).app X).left) y at ht
      rw [hp] at ht
      exact ht
    exact ⟨t, congrArg (fun a => (nativeAffineSection R X 0).left a) hy⟩

/-- The complement of the last zero coordinate on the old support is
covered by the old open times the affine line and the whole Laurent cylinder. -/
theorem range_appendZeroSection_complement :
    Set.range (closedPairOpenInclusion (appendZeroSection R z).left).left =
      Set.range (affineLineCylinder.map (closedPairOpenInclusion z.left)).left ∪
        Set.range (openInclusion.app X).left := by
  rw [range_closedPairOpenInclusion, range_appendZeroSection, Set.compl_inter,
    ← Set.preimage_compl, range_nativeAffineSection_zero, compl_compl,
    Scheme.range_fst_of_isPullback
      (affineLineCylinder_map_isPullback (closedPairOpenInclusion z.left)),
    ← range_closedPairOpenInclusion z.left]
  rfl

/-- The relative affine cylinder of the old open embeds into the literal complement. -/
def appendZeroAffineOpen :
    affineLineCylinder.obj ((opensFunctor X).obj (closedPairOpen z.left)) ⟶
      (opensFunctor (affineLineCylinder.obj X)).obj
        (closedPairOpen (appendZeroSection R z).left) := by
  let a := affineLineCylinder.map (closedPairOpenInclusion z.left)
  let v := closedPairOpenInclusion (appendZeroSection R z).left
  let i := IsOpenImmersion.lift v.left a.left (by
    rw [range_appendZeroSection_complement]
    exact Set.subset_union_left)
  exact homMk i (by
    rw [← MorphismProperty.Over.w v, ← Category.assoc, IsOpenImmersion.lift_fac,
      MorphismProperty.Over.w])

/-- The whole relative Laurent product embeds into the literal complement. -/
def appendZeroLaurentOpen :
    torusCylinder.obj X ⟶
      (opensFunctor (affineLineCylinder.obj X)).obj
        (closedPairOpen (appendZeroSection R z).left) := by
  let a := openInclusion.app X
  let v := closedPairOpenInclusion (appendZeroSection R z).left
  let i := IsOpenImmersion.lift v.left a.left (by
    rw [range_appendZeroSection_complement]
    exact Set.subset_union_right)
  exact homMk i (by
    rw [← MorphismProperty.Over.w v, ← Category.assoc, IsOpenImmersion.lift_fac,
      MorphismProperty.Over.w])

/-- The affine chart map is the original affine cylinder inclusion. -/
@[reassoc]
theorem appendZeroAffineOpen_comp :
    appendZeroAffineOpen R z ≫ closedPairOpenInclusion (appendZeroSection R z).left =
      affineLineCylinder.map (closedPairOpenInclusion z.left) :=
  MorphismProperty.Over.Hom.ext (IsOpenImmersion.lift_fac _ _ _)

/-- The Laurent chart map is the original puncture of the affine cylinder. -/
@[reassoc]
theorem appendZeroLaurentOpen_comp :
    appendZeroLaurentOpen R z ≫ closedPairOpenInclusion (appendZeroSection R z).left =
      openInclusion.app X :=
  MorphismProperty.Over.Hom.ext (IsOpenImmersion.lift_fac _ _ _)

variable {Z' X' : Sm(R)} {z' : Z' ⟶ X'} [IsClosedImmersion z'.left]
  {a : Z ⟶ Z'} {b : X ⟶ X'} (h : IsPullback z.left a.left b.left z'.left)

omit [IsNoetherian (S(R))] [IsClosedImmersion z.left] [IsClosedImmersion z'.left] in
include h in
/-- The appended zero coordinate preserves the pullback of the old closed support. -/
theorem appendZeroSection_isPullback :
    IsPullback (appendZeroSection R z).left a.left (affineLineCylinder.map b).left
      (appendZeroSection R z').left := by
  let π := projection (SmoothSite.additiveGroupObject (S(R)))
  have h₀ : IsPullback (nativeAffineSection R X 0).left b.left
      (affineLineCylinder.map b).left (nativeAffineSection R X' 0).left := by
    apply IsPullback.of_right (h₁₂ := (π.app X).left) (h₂₂ := (π.app X').left)
    · rw [show (nativeAffineSection R X 0).left ≫ (π.app X).left = 𝟙 _ from
          congrArg (fun f => f.left) (nativeAffineSection_projection R X 0),
        show (nativeAffineSection R X' 0).left ≫ (π.app X').left = 𝟙 _ from
          congrArg (fun f => f.left) (nativeAffineSection_projection R X' 0)]
      exact IsPullback.of_id_fst
    · exact congrArg (fun f => f.left) (nativeAffineSection_naturality R b 0)
    · exact (affineLineCylinder_map_isPullback b).flip
  exact h.paste_horiz h₀

/-- The affine chart inclusion is natural for a map of the original closed supports. -/
theorem appendZeroAffineOpen_naturality :
    appendZeroAffineOpen R z ≫ closedPairOpenMap (appendZeroSection_isPullback R z h) =
      affineLineCylinder.map (closedPairOpenMap h) ≫ appendZeroAffineOpen R z' := by
  let v := closedPairOpenInclusion (appendZeroSection R z').left
  let : Mono v := (forgetScheme _).mono_of_mono_map (inferInstanceAs (Mono v.left))
  apply (cancel_mono v).mp
  rw [Category.assoc, closedPairOpenMap_comm, ← Category.assoc, appendZeroAffineOpen_comp,
    Category.assoc, appendZeroAffineOpen_comp, ← Functor.map_comp, ← Functor.map_comp,
    closedPairOpenMap_comm]

/-- The Laurent chart inclusion commutes with the original ambient cylinder map. -/
theorem appendZeroLaurentOpen_naturality :
    appendZeroLaurentOpen R z ≫ closedPairOpenMap (appendZeroSection_isPullback R z h) =
      torusCylinder.map b ≫ appendZeroLaurentOpen R z' := by
  let v := closedPairOpenInclusion (appendZeroSection R z').left
  let : Mono v := (forgetScheme _).mono_of_mono_map (inferInstanceAs (Mono v.left))
  apply (cancel_mono v).mp
  rw [Category.assoc, closedPairOpenMap_comm, ← Category.assoc, appendZeroLaurentOpen_comp,
    Category.assoc, appendZeroLaurentOpen_comp]
  exact (openInclusion.naturality b).symm

omit h

instance appendZeroAffineOpen_isOpenImmersion :
    IsOpenImmersion (appendZeroAffineOpen R z).left := by
  let f := (appendZeroAffineOpen R z).left
  let g := (closedPairOpenInclusion (appendZeroSection R z).left).left
  let : IsOpenImmersion (f ≫ g) := by
    rw [show f ≫ g = (affineLineCylinder.map (closedPairOpenInclusion z.left)).left from
      congrArg (fun a => a.left) (appendZeroAffineOpen_comp R z)]
    infer_instance
  exact IsOpenImmersion.of_comp f g

instance appendZeroLaurentOpen_isOpenImmersion :
    IsOpenImmersion (appendZeroLaurentOpen R z).left := by
  let f := (appendZeroLaurentOpen R z).left
  let g := (closedPairOpenInclusion (appendZeroSection R z).left).left
  let : IsOpenImmersion (f ≫ g) := by
    rw [show f ≫ g = (openInclusion.app X).left from
      congrArg (fun a => a.left) (appendZeroLaurentOpen_comp R z)]
    infer_instance
  exact IsOpenImmersion.of_comp f g

/-- The two original chart maps cover the complementary open. -/
theorem appendZeroOpen_range_cover :
    Set.range (appendZeroAffineOpen R z).left ∪
      Set.range (appendZeroLaurentOpen R z).left = Set.univ := by
  let v := closedPairOpenInclusion (appendZeroSection R z).left
  ext x
  constructor
  · intro _
    exact Set.mem_univ _
  · intro _
    have hx : v.left x ∈ Set.range v.left := Set.mem_range_self x
    rw [range_appendZeroSection_complement] at hx
    rcases hx with ⟨y, hy⟩ | ⟨y, hy⟩
    · apply Or.inl
      refine ⟨y, v.left.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply]
      exact (congrArg (fun f => f.left y) (appendZeroAffineOpen_comp R z)).trans hy
    · apply Or.inr
      refine ⟨y, v.left.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply]
      exact (congrArg (fun f => f.left y) (appendZeroLaurentOpen_comp R z)).trans hy

/-- The overlap is the Laurent cylinder of the old open, with its actual maps. -/
theorem appendZeroOpen_isPullback :
    let j := closedPairOpenInclusion z.left
    IsPullback (openInclusion.app ((opensFunctor X).obj (closedPairOpen z.left)))
      (torusCylinder.map j) (appendZeroAffineOpen R z) (appendZeroLaurentOpen R z) := by
  let j := closedPairOpenInclusion z.left
  let i := appendZeroAffineOpen R z
  let l := appendZeroLaurentOpen R z
  let v := closedPairOpenInclusion (appendZeroSection R z).left
  let U := (opensFunctor X).obj (closedPairOpen z.left)
  let o := openInclusion.app U
  have h : o.left ≫ i.left =
      (torusCylinder.map j).left ≫ l.left := by
    apply (cancel_mono v.left).1
    rw [Category.assoc, Category.assoc,
      show i.left ≫ v.left = (affineLineCylinder.map j).left from
        congrArg (fun a => a.left) (appendZeroAffineOpen_comp R z),
      show l.left ≫ v.left = (openInclusion.app X).left from
        congrArg (fun a => a.left) (appendZeroLaurentOpen_comp R z)]
    exact congrArg (fun a => a.left) (openInclusion.naturality j).symm
  apply IsPullback.of_map_of_faithful (forgetScheme (S(R)))
  change IsPullback o.left
    (torusCylinder.map j).left i.left l.left
  have hG := parameterProduct_map_isPullback (SmoothSite.multiplicativeGroupObject (S(R))) j
  have hA := affineLineCylinder_map_isPullback j
  let p := (projection A(R)).app X
  let p₀ := (projection A(R)).app U
  let p' := projection (SmoothSite.multiplicativeGroupObject (S(R)))
  have hp₀ : o.left ≫ p₀.left = (p'.app U).left :=
    congrArg (fun f => f.left) (openInclusion_projection U)
  have hp₁ : (openInclusion.app X).left ≫ p.left = (p'.app X).left :=
    congrArg (fun f => f.left) (openInclusion_projection X)
  have H : IsPullback o.left
      (torusCylinder.map j).left (affineLineCylinder.map j).left (openInclusion.app X).left := by
    apply IsPullback.of_right (h₁₂ := p₀.left)
      (h₂₂ := p.left) (v₁₃ := j.left) (h₂₁ := (openInclusion.app X).left)
    · rw [hp₀, hp₁]
      exact hG.flip
    · exact congrArg (fun a => a.left) (openInclusion.naturality j).symm
    · exact hA.flip
  have hi : i.left ≫ v.left = (affineLineCylinder.map j).left :=
    congrArg (fun a => a.left) (appendZeroAffineOpen_comp R z)
  have hl : l.left ≫ v.left = (openInclusion.app X).left :=
    congrArg (fun a => a.left) (appendZeroLaurentOpen_comp R z)
  let r := o.left
  let t := (torusCylinder.map j).left
  have hH : IsPullback r t (i.left ≫ v.left) (l.left ≫ v.left) := by rw [hi, hl]; exact H
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk h ?_ ?_ ?_ ?_)
  · intro T
    exact hH.lift T.fst T.snd (by
      have hT := congrArg (fun f => f ≫ v.left) T.condition
      simpa only [Category.assoc] using hT)
  · intro T
    exact hH.lift_fst _ _ _
  · intro T
    exact hH.lift_snd _ _ _
  · intro T f hf hg
    exact hH.hom_ext (hf.trans (hH.lift_fst _ _ _).symm)
      (hg.trans (hH.lift_snd _ _ _).symm)

end AlgebraicGeometry.Scheme.SmoothSite.Contraction
