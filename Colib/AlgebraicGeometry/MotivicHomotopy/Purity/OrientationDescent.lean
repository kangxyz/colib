/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.PairOpenCover
public import Colib.CategoryTheory.Triangulated.SignedShift
public import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Descent of a relative orientation class

Two supported classes that agree on the overlap lift through the
Mayer–Vietoris triangle. The negative-degree group on the overlap controls
uniqueness of the lift.
-/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry.Scheme CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Sm(" k ")" => SmoothSite (Spec (CommRingCat.of k))

section Finite

variable {C : Type*} [Category C] [HasZeroObject C] [Preadditive C] [HasBinaryBiproducts C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {O : Type*} [DistribLattice O]
  (P : O ⥤ C) (A : C)

/-- The original restriction along an inequality in the lattice. -/
abbrev restrictionHom (W V : O) (h : V ≤ W) (s : P.obj W ⟶ A) : P.obj V ⟶ A :=
  P.map (homOfLE h) ≫ s

local notation "res" => restrictionHom P A

/-- The specified maps in a binary restriction triangle, in their original order. -/
structure BinaryRestrictionTriangle (V W : O) where
  /-- The boundary from the union to the shifted intersection. -/
  connecting : P.obj (V ⊔ W) ⟶ (P.obj (V ⊓ W))⟦(1 : ℤ)⟧
  distinguished :
    Triangle.mk
      (biprod.lift (P.map (homOfLE (inf_le_left : V ⊓ W ≤ V)))
        (-P.map (homOfLE (inf_le_right : V ⊓ W ≤ W))))
      (biprod.desc (P.map (homOfLE (le_sup_left : V ≤ V ⊔ W)))
        (P.map (homOfLE (le_sup_right : W ≤ V ⊔ W))))
      connecting ∈ distTriang C

variable {P A}

omit [HasZeroObject C] [Preadditive C] [HasBinaryBiproducts C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
private theorem restrict_comp {U V W : O} (h : U ≤ V) (h' : V ≤ W) (s : P.obj W ⟶ A) :
    res V U h (res W V h' s) = res W U (h.trans h') s := by
  dsimp only [restrictionHom]
  rw [← Category.assoc, ← P.map_comp, homOfLE_comp]

/-- Agreeing sections lift to the union using the specified original restriction maps. -/
theorem BinaryRestrictionTriangle.glue {V W : O} (T : BinaryRestrictionTriangle P V W)
    (s : P.obj V ⟶ A) (t : P.obj W ⟶ A)
    (h : res V (V ⊓ W) inf_le_left s = res W (V ⊓ W) inf_le_right t) :
    ∃ u : P.obj (V ⊔ W) ⟶ A, res _ V le_sup_left u = s ∧ res _ W le_sup_right u = t := by
  have hz : (biprod.lift (P.map (homOfLE (inf_le_left : V ⊓ W ≤ V)))
      (-P.map (homOfLE (inf_le_right : V ⊓ W ≤ W)))) ≫ biprod.desc s t = 0 := by
    dsimp only [restrictionHom] at h
    rw [biprod.lift_desc, Preadditive.neg_comp, h, add_neg_cancel]
  obtain ⟨u, hu⟩ := Triangle.yoneda_exact₂ _ T.distinguished (biprod.desc s t) hz
  refine ⟨u, ?_, ?_⟩
  · simpa only [Triangle.mk_mor₂, biprod.inl_desc, biprod.inl_desc_assoc] using
      congrArg ((biprod.inl : P.obj V ⟶ P.obj V ⊞ P.obj W) ≫ ·) hu.symm
  · simpa only [Triangle.mk_mor₂, biprod.inr_desc, biprod.inr_desc_assoc] using
      congrArg ((biprod.inr : P.obj W ⟶ P.obj V ⊞ P.obj W) ≫ ·) hu.symm

/-- Restrictions to a binary cover detect equality when the shifted overlap has zero Hom. -/
theorem BinaryRestrictionTriangle.hom_ext {V W : O} (T : BinaryRestrictionTriangle P V W)
    (hz : Subsingleton ((P.obj (V ⊓ W))⟦(1 : ℤ)⟧ ⟶ A))
    {u v : P.obj (V ⊔ W) ⟶ A}
    (h₁ : res _ V le_sup_left u = res _ V le_sup_left v)
    (h₂ : res _ W le_sup_right u = res _ W le_sup_right v) : u = v := by
  let b := biprod.desc (P.map (homOfLE (le_sup_left : V ≤ V ⊔ W)))
    (P.map (homOfLE (le_sup_right : W ≤ V ⊔ W)))
  have h : b ≫ u = b ≫ v := by
    apply biprod.hom_ext'
    · simpa only [b, biprod.inl_desc_assoc] using h₁
    · simpa only [b, biprod.inr_desc_assoc] using h₂
  have h' : b ≫ (u - v) = 0 := by rw [Preadditive.comp_sub, h, sub_self]
  obtain ⟨θ, hθ⟩ := Triangle.yoneda_exact₃ _ T.distinguished (u - v) h'
  exact sub_eq_zero.mp (hθ.trans (by rw [hz.elim θ 0, comp_zero]))

/-- Relative Mayer–Vietoris gives the negative-degree vanishing on a union
from vanishing on its two pieces and their intersection. -/
theorem BinaryRestrictionTriangle.shift_hom_subsingleton {V W : O}
    (T : BinaryRestrictionTriangle P V W) (a : ℤ)
    (hV : Subsingleton ((P.obj V)⟦a⟧ ⟶ A))
    (hW : Subsingleton ((P.obj W)⟦a⟧ ⟶ A))
    (hI : Subsingleton ((P.obj (V ⊓ W))⟦1 + a⟧ ⟶ A)) :
    Subsingleton ((P.obj (V ⊔ W))⟦a⟧ ⟶ A) := by
  let G := shiftFunctor C a
  let T₀ := Triangle.mk
    (biprod.lift (P.map (homOfLE (inf_le_left : V ⊓ W ≤ V)))
      (-P.map (homOfLE (inf_le_right : V ⊓ W ≤ W))))
    (biprod.desc (P.map (homOfLE (le_sup_left : V ≤ V ⊔ W)))
      (P.map (homOfLE (le_sup_right : W ≤ V ⊔ W))))
    T.connecting
  let U := G.mapTriangle.obj T₀
  have hU : U ∈ distTriang C := G.map_distinguished _ T.distinguished
  let : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBiproducts G
  let e := G.mapBiprod (P.obj V) (P.obj W)
  have hmiddle : Subsingleton (U.obj₂ ⟶ A) := ⟨fun f g => by
    apply (cancel_epi e.inv).mp
    apply biprod.hom_ext'
    · simpa only [Category.assoc] using hV.elim
        (biprod.inl ≫ e.inv ≫ f) (biprod.inl ≫ e.inv ≫ g)
    · simpa only [Category.assoc] using hW.elim
        (biprod.inr ≫ e.inv ≫ f) (biprod.inr ≫ e.inv ≫ g)⟩
  have hinter : Subsingleton (U.obj₁⟦(1 : ℤ)⟧ ⟶ A) := by
    let q := ((shiftFunctorAdd' C a 1 (1 + a) (add_comm a 1)).app (P.obj (V ⊓ W))).hom
    exact ⟨fun f g => (cancel_epi q).mp (hI.elim (q ≫ f) (q ≫ g))⟩
  refine ⟨fun f g => ?_⟩
  obtain ⟨δ, hδ⟩ := U.yoneda_exact₃ hU (f - g) (hmiddle.elim _ 0)
  exact sub_eq_zero.mp (hδ.trans (by rw [hinter.elim δ 0, comp_zero]))

variable [OrderBot O]

omit [OrderBot O] in
private theorem restrict_iso_of_eq {X Y : O} (e : X = Y) : IsIso (homOfLE (le_of_eq e)) := by
  subst Y
  exact (show IsIso (𝟙 X) from inferInstance)

private theorem restrict_eq_of_cover {ι : Type*} (cover : ι → O) (s : Finset ι)
    (T : ∀ V W, BinaryRestrictionTriangle P V W)
    (hbot : Subsingleton (P.obj ⊥ ⟶ A))
    (hz : ∀ V, Subsingleton ((P.obj V)⟦(1 : ℤ)⟧ ⟶ A))
    {u v : P.obj (s.sup cover) ⟶ A}
    (h : ∀ i (hi : i ∈ s),
      res _ (cover i) (Finset.le_sup hi) u = res _ (cover i) (Finset.le_sup hi) v) :
    u = v := by
  classical
  revert u v
  induction s using Finset.induction_on with
  | empty =>
      intro u v _
      let e : (∅ : Finset ι).sup cover = ⊥ := Finset.sup_empty
      let := restrict_iso_of_eq e.symm
      let j := P.map (homOfLE (le_of_eq e.symm))
      let : IsIso j := inferInstanceAs (IsIso (P.map (homOfLE (le_of_eq e.symm))))
      apply (cancel_epi j).1
      exact hbot.elim _ _
  | @insert i s hi ih =>
      intro u v h
      let e : (insert i s).sup cover = cover i ⊔ s.sup cover := Finset.sup_insert
      let j := le_of_eq e.symm
      let : IsIso (homOfLE j) := restrict_iso_of_eq e.symm
      apply (cancel_epi (P.map (homOfLE j))).1
      change res _ _ j u = res _ _ j v
      apply (T (cover i) (s.sup cover)).hom_ext (hz _)
      · rw [restrict_comp, restrict_comp]
        exact h i (Finset.mem_insert_self i s)
      · apply ih
        intro j' hj'
        rw [restrict_comp, restrict_comp, restrict_comp, restrict_comp]
        exact h j' (Finset.mem_insert_of_mem hj')

/-- Compatible sections on the actual smaller opens glue over a finite union.
The negative group is needed for uniqueness on every overlap in the induction. -/
theorem existsUnique_glue_finset {ι : Type*} (cover : ι → O) (s : Finset ι)
    (T : ∀ V W, BinaryRestrictionTriangle P V W)
    (hbot : Subsingleton (P.obj ⊥ ⟶ A))
    (hz : ∀ V, Subsingleton ((P.obj V)⟦(1 : ℤ)⟧ ⟶ A))
    (x : ∀ i, P.obj (cover i) ⟶ A)
    (hx : ∀ i j, res _ _ (inf_le_left : cover i ⊓ cover j ≤ cover i) (x i) =
      res _ _ (inf_le_right : cover i ⊓ cover j ≤ cover j) (x j)) :
    ∃! u : P.obj (s.sup cover) ⟶ A, ∀ i (hi : i ∈ s),
      res _ (cover i) (Finset.le_sup hi) u = x i := by
  classical
  suffices ∃ u : P.obj (s.sup cover) ⟶ A, ∀ i (hi : i ∈ s),
      res _ (cover i) (Finset.le_sup hi) u = x i by
    obtain ⟨u, hu⟩ := this
    exact ⟨u, hu, fun v hv => restrict_eq_of_cover cover s T hbot hz
      (fun i hi => (hv i hi).trans (hu i hi).symm)⟩
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      simp
  | @insert i s hi ih =>
      obtain ⟨v, hv⟩ := ih
      let V := cover i
      let W := s.sup cover
      let B := V ⊓ W
      have allSup (t : Finset ι) : t.sup (fun j => V ⊓ cover j) = V ⊓ t.sup cover := by
        induction t using Finset.induction_on with
        | empty => simp
        | @insert j t hj ht => rw [Finset.sup_insert, Finset.sup_insert, inf_sup_left, ht]
      have eqB : s.sup (fun j => V ⊓ cover j) = B := allSup s
      have hb := le_of_eq eqB
      have huB : res V _ (hb.trans inf_le_left) (x i) =
          res W _ (hb.trans inf_le_right) v := by
        apply restrict_eq_of_cover (fun j => V ⊓ cover j) s T hbot hz
        intro j hj
        rw [restrict_comp, restrict_comp]
        have hm : (V ⊓ cover j) ≤ W := inf_le_right.trans (Finset.le_sup hj)
        have h₀ : res W (V ⊓ cover j) hm v = res (cover j) (V ⊓ cover j) inf_le_right (x j) := by
          rw [← restrict_comp inf_le_right (Finset.le_sup hj), hv j hj]
        exact (hx i j).trans h₀.symm
      have hB : res V B inf_le_left (x i) = res W B inf_le_right v := by
        let : IsIso (homOfLE hb) := restrict_iso_of_eq eqB
        apply (cancel_epi (P.map (homOfLE hb))).1
        change res _ _ hb (res V B inf_le_left (x i)) = res _ _ hb (res W B inf_le_right v)
        rw [restrict_comp, restrict_comp]
        exact huB
      obtain ⟨u, hu, hu'⟩ := (T V W).glue (x i) v hB
      let e : (insert i s).sup cover = V ⊔ W := Finset.sup_insert
      refine ⟨res _ _ (le_of_eq e) u, ?_⟩
      intro j hj
      rw [restrict_comp]
      rcases Finset.mem_insert.1 hj with rfl | hj'
      · exact hu
      · exact (restrict_comp (Finset.le_sup hj') le_sup_right u).symm.trans
          ((congrArg (res W (cover j) (Finset.le_sup hj')) hu').trans (hv j hj'))

end Finite

section OpenRestrictions

-- Use the native transfer Abelian structure in the original restricted pair.
/-- The canonical abelian structure on sheaves with transfers. -/
local instance orientationDescentAbelian : Abelian (LargeSheaves k) := SheafWithTransfers.abelian k

-- Keep the represented transfers opaque while identifying the four corners.
attribute [local irreducible] Cor.graphFunctor transferRepresentable

variable {Y V : Sm(k)} (p : V ⟶ Y) {U : Sm(k)} (j : U ⟶ V)

open SmoothSite

/-- The original relative pair restricted over each open of the base of its support. -/
@[expose] def relativeOpenRestrictionPair : Y.left.Opens ⥤ Arrow Sm(k) where
  obj W := Arrow.mk (preimageOpenMap V j (p.left ⁻¹ᵁ W))
  map {W W'} f := Arrow.homMk'
    ((opensFunctor U).map (homOfLE (j.left.preimage_mono (p.left.preimage_mono f.le))))
    ((opensFunctor V).map (homOfLE (p.left.preimage_mono f.le)))
    (preimageOpenMap_naturality V j (p.left.preimage_mono f.le))
  map_id W := by
    apply Arrow.hom_ext
    · exact (opensFunctor U).map_id _
    · exact (opensFunctor V).map_id _
  map_comp f g := by
    apply Arrow.hom_ext
    · exact (opensFunctor U).map_comp
        (homOfLE (j.left.preimage_mono (p.left.preimage_mono f.le)))
        (homOfLE (j.left.preimage_mono (p.left.preimage_mono g.le)))
    · exact (opensFunctor V).map_comp
        (homOfLE (p.left.preimage_mono f.le)) (homOfLE (p.left.preimage_mono g.le))

/-- The relative motive of each restricted pair, with the actual restriction maps
in the variable of its opens. -/
abbrev relativeOpenRestrictionMotive : Y.left.Opens ⥤ EffectiveMotivesMinus k :=
  relativeOpenRestrictionPair k p j ⋙ effectivePairMotiveFunctor k

variable [IsOpenImmersion j.left]

/-- The original motive of a pair is its relative restriction over the whole base. -/
def relativeOpenRestrictionTopIso :
    (relativeOpenRestrictionMotive k p j).obj ⊤ ≅ effectivePairMotive k j := by
  let W := p.left ⁻¹ᵁ (⊤ : Y.left.Opens)
  let a := pairArrowOpenInclusion j W
  have hW : W = ⊤ := AlgebraicGeometry.Scheme.Hom.preimage_top p.left
  have hU : j.left ⁻¹ᵁ W = ⊤ := by rw [hW, AlgebraicGeometry.Scheme.Hom.preimage_top]
  have topIso {D : Sm(k)} (V : D.left.Opens) (hV : V = ⊤) :
      IsIso (openInclusion D V) := by
    subst V
    refine @isIso_of_reflects_iso _ _ _ _ _ _ (openInclusion D ⊤) (forgetScheme _) ?_ _
    exact inferInstanceAs (IsIso D.left.topIso.hom)
  let : IsIso a.left := by
    change IsIso (openInclusion U (j.left ⁻¹ᵁ W))
    exact topIso _ hU
  let : IsIso a.right := by
    change IsIso (openInclusion V W)
    exact topIso _ hW
  let : IsIso a := Arrow.isIso_of_isIso_left_of_isIso_right a
  exact (effectivePairMotiveFunctor k).mapIso (asIso a)

omit [IsOpenImmersion j.left] in
/-- The restricted motive over the empty open vanishes. -/
theorem isZero_relativeOpenRestrictionMotive_bot :
    IsZero ((relativeOpenRestrictionMotive k p j).obj ⊥) := by
  let W := p.left ⁻¹ᵁ (⊥ : Y.left.Opens)
  let q := preimageOpenMap V j W
  let : IsEmpty ((opensFunctor V).obj W).left := by
    change IsEmpty W.toScheme
    rw [show W = ⊥ from AlgebraicGeometry.Scheme.Hom.preimage_bot p.left]
    exact ⟨fun x => x.property⟩
  let : IsIso q := by
    refine @isIso_of_reflects_iso _ _ _ _ _ _ q (forgetScheme _) ?_ _
    exact inferInstanceAs (IsIso q.left)
  exact (effectiveTransferSheaf k).map_isZero
    (isZero_cokernel_of_epi ((smoothTransferRepresentable k).map q))

set_option maxHeartbeats 1150000 in
-- Supply the cover data before comparing the chosen triangle with its four restricted pairs.
omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory (LargeSheaves k)]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
/-- Pulling back the original open cover gives a short exact transfer quotient row. -/
theorem relativeOpenRestrictionCover_shortExact (W W' : Y.left.Opens) :
    (transferPairOpenCoverSequence k
      (preimageOpenUnionCoverMap V (p.left ⁻¹ᵁ W) (p.left ⁻¹ᵁ W') j)).ShortExact := by
  let A := openUnionCoverSquare U (j.left ⁻¹ᵁ (p.left ⁻¹ᵁ W)) (j.left ⁻¹ᵁ (p.left ⁻¹ᵁ W'))
  let B := openUnionCoverSquare V (p.left ⁻¹ᵁ W) (p.left ⁻¹ᵁ W')
  let f : A ⟶ B := preimageOpenUnionCoverMap V (p.left ⁻¹ᵁ W) (p.left ⁻¹ᵁ W') j
  let : IsOpenImmersion f.τ₁.left := inferInstanceAs
    (IsOpenImmersion (preimageOpenMap V j (p.left ⁻¹ᵁ W ⊓ p.left ⁻¹ᵁ W')).left)
  let : IsOpenImmersion f.τ₂.left := inferInstanceAs
    (IsOpenImmersion (preimageOpenMap V j (p.left ⁻¹ᵁ W)).left)
  let : IsOpenImmersion f.τ₃.left := inferInstanceAs
    (IsOpenImmersion (preimageOpenMap V j (p.left ⁻¹ᵁ W')).left)
  let : IsOpenImmersion f.τ₄.left := inferInstanceAs
    (IsOpenImmersion (preimageOpenMap V j (p.left ⁻¹ᵁ W ⊔ p.left ⁻¹ᵁ W')).left)
  exact transferPairOpenCoverSequence_shortExact k f
    (openUnionCoverSquare_isPullback U _ _) (openUnionCoverSquare_isPullback V _ _)
    (openUnionCoverSquare_range_cover U _ _) (openUnionCoverSquare_range_cover V _ _)

set_option maxHeartbeats 850000 in
-- Read the four maps after pinning the actual arrow square and quotient functor.
private theorem relativeOpenRestrictionTriangle_maps (W W' : Y.left.Opens) :
    let X := effectivePairOpenCoverTriangle k (relativeOpenRestrictionCover_shortExact k p j W W')
    let P := relativeOpenRestrictionMotive k p j
    let a := P.map (homOfLE (inf_le_left : W ⊓ W' ≤ W))
    let b := P.map (homOfLE (inf_le_right : W ⊓ W' ≤ W'))
    let c := P.map (homOfLE (le_sup_left : W ≤ W ⊔ W'))
    let d := P.map (homOfLE (le_sup_right : W' ≤ W ⊔ W'))
    X.mor₁ = biprod.lift a (-b) ∧ X.mor₂ = biprod.desc c d := by
  intro X P a b c d
  let f := preimageOpenUnionCoverMap V (p.left ⁻¹ᵁ W) (p.left ⁻¹ᵁ W') j
  let Q₀ := arrowSquare f
  let F := effectivePairMotiveFunctor k
  have h₁ : F.map Q₀.f₁₂ = a := rfl
  have h₂ : F.map Q₀.f₁₃ = b := rfl
  have h₃ : F.map Q₀.f₂₄ = c := rfl
  have h₄ : F.map Q₀.f₃₄ = d := rfl
  constructor
  · change biprod.lift (F.map Q₀.f₁₂) (-F.map Q₀.f₁₃) = biprod.lift a (-b)
    exact congrArg₂ biprod.lift h₁ (congrArg Neg.neg h₂)
  · change biprod.desc (F.map Q₀.f₂₄) (F.map Q₀.f₃₄) = biprod.desc c d
    exact congrArg₂ biprod.desc h₃ h₄

set_option maxHeartbeats 1300000 in
-- The four vertices retain their actual quotient motives from the represented cover.
/-- The two-cover triangle for the actual relative motive of a restricted pair. -/
def relativeOpenRestrictionTriangle (W W' : Y.left.Opens) :
    BinaryRestrictionTriangle (relativeOpenRestrictionMotive k p j) W W' := by
  let h := relativeOpenRestrictionCover_shortExact k p j W W'
  let T := effectivePairOpenCoverTriangle k h
  have hm := relativeOpenRestrictionTriangle_maps k p j W W'
  let P := relativeOpenRestrictionMotive k p j
  let a := P.map (homOfLE (inf_le_left : W ⊓ W' ≤ W))
  let b := P.map (homOfLE (inf_le_right : W ⊓ W' ≤ W'))
  let c := P.map (homOfLE (le_sup_left : W ≤ W ⊔ W'))
  let d := P.map (homOfLE (le_sup_right : W' ≤ W ⊔ W'))
  let δ : P.obj (W ⊔ W') ⟶ (P.obj (W ⊓ W'))⟦(1 : ℤ)⟧ := T.mor₃
  let T' : Triangle (EffectiveMotivesMinus k) :=
    Triangle.mk (biprod.lift a (-b)) (biprod.desc c d) δ
  have he : T = T' := by
    change Triangle.mk T.mor₁ T.mor₂ δ = T'
    exact congrArg₂ (fun f g => Triangle.mk f g δ) hm.1 hm.2
  have ht : T ∈ distTriang (EffectiveMotivesMinus k) :=
    effectivePairOpenCoverTriangle_distinguished k h
  have ht' : T' ∈ distTriang (EffectiveMotivesMinus k) := he ▸ ht
  exact ⟨δ, ht'⟩

end OpenRestrictions

end AlgebraicGeometry.MotivicHomotopy
