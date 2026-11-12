/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# The two original sections from a marked etale chart

Pull the chosen section back along the full etale chart, then form the actual etale
refinement over the tail base. The original projection and the map through that section
produce two graph sections on the same base-changed curve. Their marking and residue-field
restrictions are equal as scheme morphisms. The supplied curve can be the unchanged
whole-fiber open while the chart is its intersection with the etale-near-point open.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.EtaleChart
variable {A Y Z : Scheme.{u}} (q : A ⟶ Z) (p : Z ⟶ Y) (s : Y ⟶ Z)

/-- The actual inverse image of the chosen coordinate section under the etale chart. -/
abbrev sectionBase := pullback s q
/-- The actual etale refinement of the chart over its tail-coordinate base. -/
abbrev refinement := pullback (q ≫ p) (pullback.fst s q)

/-- The original projection of the refinement to the chart. -/
def original : refinement q p s ⟶ A := pullback.fst _ _
/-- The map through the pulled-back coordinate section to the same original chart. -/
def retract : refinement q p s ⟶ A := pullback.snd _ _ ≫ pullback.snd s q

/-- Both original chart maps have exactly the same tail coordinates. -/
theorem retract_base (hs : s ≫ p = 𝟙 Y) :
    retract q p s ≫ (q ≫ p) = original q p s ≫ (q ≫ p) := by
  dsimp only [retract, original]
  simp only [Category.assoc]
  rw [← Category.assoc (pullback.snd s q), ← pullback.condition]
  simp only [Category.assoc, hs, Category.comp_id]
  exact pullback.condition.symm

variable {Ω : Type u} [Field Ω]
  (ξ : Spec (.of Ω) ⟶ A) (η : Spec (.of Ω) ⟶ Y)
  (hξ : ξ ≫ q = η ≫ s)

/-- The actual field-valued mark on the coordinate-section pullback. -/
def sectionMark : Spec (.of Ω) ⟶ sectionBase q s := pullback.lift η ξ hξ.symm

include hξ in
/-- The same original mark has the prescribed image under the tail projection. -/
theorem mark_base (hs : s ≫ p = 𝟙 Y) : ξ ≫ (q ≫ p) = η := by
  rw [← Category.assoc, hξ, Category.assoc, hs, Category.comp_id]

/-- The compatible original field-valued mark on the etale refinement. -/
def refinementMark (hs : s ≫ p = 𝟙 Y) : Spec (.of Ω) ⟶ refinement q p s :=
  pullback.lift ξ (sectionMark q s ξ η hξ)
    ((mark_base q p s ξ η hξ hs).trans (pullback.lift_fst _ _ _).symm)

/-- The original projection preserves the actual scheme marking. -/
theorem refinementMark_original (hs : s ≫ p = 𝟙 Y) :
    refinementMark q p s ξ η hξ hs ≫ original q p s = ξ := pullback.lift_fst _ _ _

/-- The retract preserves the same actual scheme marking. -/
theorem refinementMark_retract (hs : s ≫ p = 𝟙 Y) :
    refinementMark q p s ξ η hξ hs ≫ retract q p s = ξ := by
  simp [refinementMark, retract, sectionMark]

variable {U : Scheme.{u}} (i : A ⟶ U) (f : U ⟶ Y) (hi : i ≫ f = q ≫ p)

/-- The original relative curve after base change to the etale refinement. -/
abbrev curve := pullback (original q p s ≫ (q ≫ p)) f

/-- The graph section of the original chart map into the given curve. -/
def originalSection : refinement q p s ⟶ curve q p s f :=
  pullback.lift (𝟙 _) (original q p s ≫ i) (by simp [hi])

/-- The graph section of the coordinate-section retract into the same curve. -/
def retractSection (hs : s ≫ p = 𝟙 Y) : refinement q p s ⟶ curve q p s f :=
  pullback.lift (𝟙 _) (retract q p s ≫ i) (by
    simp only [Category.id_comp, Category.assoc, hi]
    exact (retract_base q p s hs).symm)

/-- The original graph is a section of the actual curve projection. -/
theorem originalSection_projection :
    originalSection q p s i f hi ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _

/-- The retracted graph is a section of the same curve projection. -/
theorem retractSection_projection (hs : s ≫ p = 𝟙 Y) :
    retractSection q p s i f hi hs ≫ pullback.fst _ _ = 𝟙 _ := pullback.lift_fst _ _ _

/-- The original graph retains its original target morphism. -/
theorem originalSection_target :
    originalSection q p s i f hi ≫ pullback.snd _ _ = original q p s ≫ i :=
  pullback.lift_snd _ _ _

/-- The retracted graph retains its original target morphism. -/
theorem retractSection_target (hs : s ≫ p = 𝟙 Y) :
    retractSection q p s i f hi hs ≫ pullback.snd _ _ = retract q p s ≫ i :=
  pullback.lift_snd _ _ _

/-- The two explicit sections agree after the same original field-valued mark. -/
theorem sections_same_marking (hs : s ≫ p = 𝟙 Y) :
    refinementMark q p s ξ η hξ hs ≫ originalSection q p s i f hi =
      refinementMark q p s ξ η hξ hs ≫ retractSection q p s i f hi hs := by
  apply pullback.hom_ext
  · simp [Category.assoc, originalSection_projection, retractSection_projection]
  · simp only [Category.assoc, originalSection_target, retractSection_target]
    rw [← Category.assoc, refinementMark_original]
    rw [← Category.assoc, refinementMark_retract]

/-- The two actual sections agree on the original residue field, not only on points. -/
theorem sections_same_residueField (hs : s ≫ p = 𝟙 Y) :
    (refinement q p s).fromSpecResidueField
        (refinementMark q p s ξ η hξ hs (IsLocalRing.closedPoint Ω)) ≫
      originalSection q p s i f hi =
    (refinement q p s).fromSpecResidueField
        (refinementMark q p s ξ η hξ hs (IsLocalRing.closedPoint Ω)) ≫
      retractSection q p s i f hi hs := by
  let β := refinementMark q p s ξ η hξ hs
  let e := (refinement q p s).descResidueField (Scheme.stalkClosedPointTo β)
  have : Surjective (Spec.map e) := ⟨Function.surjective_to_subsingleton _⟩
  have : Epi (Spec.map e) := Flat.epi_of_flat_of_surjective _
  apply (cancel_epi (Spec.map e)).mp
  change Spec.map ((refinement q p s).descResidueField (Scheme.stalkClosedPointTo β)) ≫ _ = _
  rw [← Category.assoc, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField,
    ← Category.assoc, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField]
  exact sections_same_marking q p s ξ η hξ i f hi hs

instance [Etale q] : Etale (original q p s) := by
  change Etale (pullback.fst (q ≫ p) (pullback.fst s q))
  infer_instance
instance [IsAffine A] [IsAffine Y] [IsAffine Z] : IsAffine (refinement q p s) := inferInstance
instance [SmoothOfRelativeDimension 1 f] :
    SmoothOfRelativeDimension 1 (pullback.fst (original q p s ≫ (q ≫ p)) f) := inferInstance
end AlgebraicGeometry.Scheme.EtaleChart
