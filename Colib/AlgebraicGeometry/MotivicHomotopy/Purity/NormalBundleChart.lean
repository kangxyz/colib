/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.VectorBundleBasisChart
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.NormalBundleSmooth
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.AffineSpaceProduct
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.ClosedPair
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.PairOpenCoverGeometry
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleAffineSpaceBundle
import Colib.AlgebraicGeometry.Scheme.CartesianRange

/-! # Marked normal charts for the original supported motives -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
open SmoothSite
open SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable {k : Type u} [Field k]

local notation "Base" => Spec (CommRingCat.of k)

variable {Z X : SmoothSite (Spec (CommRingCat.of k))} (i : Z ⟶ X) [IsClosedImmersion i.left]
  {n m : ℕ} (hX : RelativeDimension X.hom n) (hZ : RelativeDimension Z.hom m)

local notation "E" => (Stacks.Conormal.conormalSheafDegreeOne i.left : Z.left.Modules)
local notation "p" => normalBundleProjection i hX hZ
local notation "s" => normalBundleZeroSection i hX hZ
local notation "N" => normalBundle i hX hZ

include hX hZ in
/-- Every point of the original centre lies in a marked affine normal chart. -/
theorem exists_normalBundleBasisChart (x : Z.left) :
    ∃ V : Z.left.affineOpens, x ∈ V.1 ∧
      Nonempty (Module.Basis (Fin (n - m)) Γ(Z.left, V.1) Γ(E, V.1)) := by
  have hi : i.left ≫ X.hom = Z.hom := MorphismProperty.Over.w i
  let : Smooth (i.left ≫ X.hom) :=
    (congrArg (fun f => Smooth f) hi).mpr (inferInstanceAs (Smooth Z.hom))
  let hZ' : RelativeDimension (i.left ≫ X.hom) m := by
    intro y hy
    have hf : (i.left ≫ X.hom).fiber y = Z.hom.fiber y :=
      congrArg (fun f : Z.left ⟶ Base => f.fiber y) hi
    have hy' : Nonempty (Z.hom.fiber y) := hf ▸ hy
    exact hf.symm ▸ hZ y hy'
  let := Stacks.ConormalSequenceRight.isFiniteLocallyFreeOfRank_conormalSheafDegreeOne
    i.left X.hom hX hZ'
  obtain ⟨V, ha, hx, hb⟩ := Stacks.Chow.exists_isAffineOpen_basis_sections E (n - m) x
  exact ⟨⟨V, ha⟩, hx, hb⟩

variable (V : Z.left.affineOpens)

set_option quotPrecheck false in
local notation "U" =>
  (SmoothSite.opensFunctor (S := Spec (CommRingCat.of k)) Z).obj (V.1 : Z.left.Opens)

/-- The original normal zero section on the literal chart open. -/
def normalBundleZeroOn :
    (SmoothSite.opensFunctor (S := Spec (CommRingCat.of k)) Z).obj (V.1 : Z.left.Opens) ⟶
      (SmoothSite.opensFunctor (S := Spec (CommRingCat.of k)) (normalBundle i hX hZ)).obj
        ((normalBundleProjection i hX hZ).left ⁻¹ᵁ V.1) :=
  homMk (Scheme.Modules.vectorBundleZeroSectionOn E V) (by
    let v := Scheme.Modules.vectorBundleZeroSection Z.left E
    have hv : v ≫ (N).hom = Z.hom := MorphismProperty.Over.w (s)
    exact (Scheme.Modules.vectorBundleZeroSectionOn_ι_assoc E V (N).hom).trans
      (congrArg (V.1.ι ≫ ·) hv))

instance normalBundleZeroOn_isClosedImmersion :
    IsClosedImmersion (normalBundleZeroOn i hX hZ V).left :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (Scheme.Modules.vectorBundleZeroSectionOn_isPullback E V).flip
    (normalBundleZeroSectionOfSmooth_isClosedImmersion i)

/-- The marked chart maps to the original normal pair by the literal open restrictions. -/
theorem normalBundleZeroOn_isPullback :
    IsPullback (normalBundleZeroOn i hX hZ V).left V.1.ι ((p).left ⁻¹ᵁ V.1).ι (s).left :=
  Scheme.Modules.vectorBundleZeroSectionOn_isPullback E V

variable (b : Module.Basis (Fin (n - m)) Γ(Z.left, (V.1 : Z.left.Opens))
  Γ((Stacks.Conormal.conormalSheafDegreeOne i.left : Z.left.Modules), (V.1 : Z.left.Opens)))

/-- The native normal chart is identified with the original affine space over its base open. -/
def normalBundleBasisChart :
    (SmoothSite.opensFunctor (S := Spec (CommRingCat.of k)) (normalBundle i hX hZ)).obj
      ((normalBundleProjection i hX hZ).left ⁻¹ᵁ V.1) ≅
        relativeAffineSpace (U) (n - m) := by
  let e : (((p).left ⁻¹ᵁ (V.1 : Z.left.Opens))).toScheme ≅
        AffineSpace (ULift.{u} (Fin (n - m))) V.1.toScheme :=
    Scheme.Modules.vectorBundleBasisChart E V b
  refine MorphismProperty.Over.isoMk e ?_
  change e.hom ≫ (AffineSpace (ULift.{u} (Fin (n - m))) V.1.toScheme ↘ V.1.toScheme) ≫
      V.1.ι ≫ Z.hom = ((p).left ⁻¹ᵁ V.1).ι ≫ (N).hom
  let q := (p).left
  let a := (AffineSpace (ULift.{u} (Fin (n - m))) V.1.toScheme ↘ V.1.toScheme)
  have h₀ : e.hom ≫ a = q ∣_ V.1 := Scheme.Modules.vectorBundleBasisChart_hom_over E V b
  have h₁ : (q ∣_ V.1) ≫ V.1.ι ≫ Z.hom = (q ⁻¹ᵁ V.1).ι ≫ q ≫ Z.hom :=
    morphismRestrict_ι_assoc q V.1 Z.hom
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ V.1.ι ≫ Z.hom) h₀)).trans h₁

/-- The chart projection is the restriction of the original bundle projection. -/
theorem normalBundleBasisChart_projection :
    (normalBundleBasisChart i hX hZ V b).hom ≫ affineSpaceProjection U (n - m) =
      preimageOpenMap Z (p) V.1 := by
  apply MorphismProperty.Over.Hom.ext
  change (Scheme.Modules.vectorBundleBasisChart E V b).hom ≫
    (AffineSpace (ULift.{u} (Fin (n - m))) V.1.toScheme ↘ V.1.toScheme) =
      (p).left.resLE V.1 ((p).left ⁻¹ᵁ V.1) le_rfl
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact Scheme.Modules.vectorBundleBasisChart_hom_over E V b

/-- The normal-bundle basis chart identifies the full zero scheme with the origin. -/
@[reassoc]
theorem normalBundleBasisChart_zero :
    normalBundleZeroOn i hX hZ V ≫ (normalBundleBasisChart i hX hZ V b).hom =
      relativeAffineSpaceZeroSection U (n - m) := by
  apply MorphismProperty.Over.Hom.ext
  exact Scheme.Modules.vectorBundleBasisChart_zeroSection E V b

/-- The normal zero restriction has precisely the complementary open obtained
by pulling the original complement back over the chart open. -/
theorem range_normalBundleZeroOn_open :
    Set.range (closedPairOpenInclusion (normalBundleZeroOn i hX hZ V).left).left =
      Set.range (preimageOpenMap N (closedPairOpenInclusion (s).left)
        ((p).left ⁻¹ᵁ V.1)).left := by
  let q : (normalBundle i hX hZ).left.Opens :=
    (normalBundleProjection i hX hZ).left ⁻¹ᵁ (V.1 : Z.left.Opens)
  let j := closedPairOpenInclusion (s).left
  let z := normalBundleZeroOn i hX hZ V
  let v : q.toScheme ⟶ (N).left := q.ι
  have h₀ : Set.range z.left = v ⁻¹' Set.range (s).left :=
    Scheme.range_fst_of_isPullback (normalBundleZeroOn_isPullback i hX hZ V)
  have h₁ : Set.range (j.left ∣_ q) = v ⁻¹' Set.range j.left :=
    Scheme.range_fst_of_isPullback (isPullback_morphismRestrict j.left q)
  change Set.range (closedPairOpenInclusion z.left).left = Set.range (j.left.resLE q _ le_rfl)
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  calc
    _ = (Set.range z.left)ᶜ := range_closedPairOpenInclusion z.left
    _ = (v ⁻¹' Set.range (s).left)ᶜ := congrArg (·ᶜ) h₀
    _ = v ⁻¹' (Set.range (s).left)ᶜ := Set.preimage_compl.symm
    _ = v ⁻¹' Set.range j.left :=
      congrArg (v ⁻¹' ·) (range_closedPairOpenInclusion (s).left).symm
    _ = _ := h₁.symm

end AlgebraicGeometry.MotivicHomotopy
