/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodCurveSections
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChartRetainedCompactificationGeometry

/-! # Original fixed-target inputs on the genuine native chart refinement

Only the actual chart, retained curve and compactification are used. These inputs
supply sections and target recovery, not the independent full-boundary witness.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite.EtaleChart.OriginalFixed
variable {S : Scheme.{u}} {A Y Z T : SmoothSite S}
  [IsAffine A.left] [IsAffine Y.left] [IsAffine Z.left]
  (q : A ⟶ Z) [Etale q.left] (p : Z ⟶ Y) (s : Y ⟶ Z)
  {U N : Scheme.{u}} (i : A.left ⟶ U) (f : U ⟶ Y.left)
  (hi : i ≫ f = q.left ≫ p.left)
  (j : U ⟶ N) (fN : N ⟶ Y.left) (hj : j ≫ fN = f)

/-- The base is the existing native refinement object, not a replacement Spec. -/
abbrev base := refinementObject q p s
/-- The genuine pullback compactification. -/
abbrev compactification := Scheme.EtaleChart.compactifiedCurve q.left p.left s.left fN
/-- The genuine retained pullback. -/
abbrev retained := Scheme.EtaleChart.curve q.left p.left s.left f
/-- The actual compactified structure map to the native refinement. -/
abbrev compactifiedProjection : compactification q p s fN ⟶ (base q p s).left := pullback.fst _ _
/-- The previously proved Cartesian retained inclusion. -/
abbrev inclusion : retained q p s f ⟶ compactification q p s fN :=
  Scheme.EtaleChart.retainedToCompactification q.left p.left s.left f j fN hj
/-- The unchanged original section, with its genuine native source. -/
abbrev originalSection : (base q p s).left ⟶ retained q p s f :=
  Scheme.EtaleChart.originalSection q.left p.left s.left i f hi
/-- The unchanged retraction section. -/
abbrev retractSection (hs : s.left ≫ p.left = 𝟙 Y.left) :
    (base q p s).left ⟶ retained q p s f :=
  Scheme.EtaleChart.retractSection q.left p.left s.left i f hi hs

/-- The original section is a section over the actual compactified projection. -/
theorem originalSection_structure :
    originalSection q p s i f hi ≫
      (inclusion q p s f j fN hj ≫ compactifiedProjection q p s fN) = 𝟙 _ := by
  exact (Category.assoc _ _ _).symm.trans
    (Scheme.EtaleChart.compactifiedOriginalSection_projection
      q.left p.left s.left i f hi j fN hj)

/-- The original retraction is a section of that same projection. -/
theorem retractSection_structure (hs : s.left ≫ p.left = 𝟙 Y.left) :
    retractSection q p s i f hi hs ≫
      (inclusion q p s f j fN hj ≫ compactifiedProjection q p s fN) = 𝟙 _ := by
  exact (Category.assoc _ _ _).symm.trans
    (Scheme.EtaleChart.compactifiedRetractSection_projection
      q.left p.left s.left i f hi j fN hj hs)

/-- Their field-valued common mark is the existing native refinement mark. -/
theorem sections_common_mark {Ω : Type u} [Field Ω]
    (ξ : Spec (.of Ω) ⟶ A.left) (η : Spec (.of Ω) ⟶ Y.left)
    (hξ : ξ ≫ q.left = η ≫ s.left) (hs : s.left ≫ p.left = 𝟙 Y.left) :
    refinementMark q p s ξ η hξ hs ≫
      (originalSection q p s i f hi ≫ inclusion q p s f j fN hj) =
    refinementMark q p s ξ η hξ hs ≫
      (retractSection q p s i f hi hs ≫ inclusion q p s f j fN hj) :=
  Scheme.EtaleChart.compactifiedSections_same_marking q.left p.left s.left
    i f hi j fN hj ξ η hξ hs

variable (t : U ⟶ T.left) (ht : t ≫ T.hom = f ≫ Y.hom)

/-- The chart's original target arrow over the original base S. -/
def chartTarget : A ⟶ T := homMk (i ≫ t) (by
  rw [Category.assoc, ht, ← Category.assoc i, hi, Category.assoc,
    MorphismProperty.Over.w p, MorphismProperty.Over.w q])

/-- The original native projection target arrow. -/
def originalTarget : base q p s ⟶ T :=
  refinementToChart q p s ≫ chartTarget q p i f hi t ht
/-- The original native retract target arrow. -/
def retractTarget : base q p s ⟶ T :=
  (refinementToSection q p s ≫ sectionToChart q s) ≫ chartTarget q p i f hi t ht

/-- The target on the entire retained curve, not only on the etale chart. -/
abbrev retainedTarget : retained q p s f ⟶ T.left := pullback.snd _ _ ≫ t

include ht in
/-- The retained target is over S with the actual refinement structure. -/
theorem retainedTarget_over_base :
    retainedTarget q p s f t ≫ T.hom =
      inclusion q p s f j fN hj ≫ compactifiedProjection q p s fN ≫ (base q p s).hom := by
  have hb : (Scheme.EtaleChart.original q.left p.left s.left ≫
      (q.left ≫ p.left)) ≫ Y.hom = (base q p s).hom :=
    MorphismProperty.Over.w (refinementToChart q p s ≫ (q ≫ p))
  let h : (base q p s).left ⟶ Y.left :=
    Scheme.EtaleChart.original q.left p.left s.left ≫ (q.left ≫ p.left)
  let C : Scheme := pullback h f
  let v : C ⟶ U := pullback.snd h f
  let π : C ⟶ (base q p s).left := pullback.fst h f
  have hw : v ≫ f = π ≫ h := (pullback.condition (f := h) (g := f)).symm
  change (v ≫ t) ≫ T.hom = _
  have hcalc : (v ≫ t) ≫ T.hom = π ≫ (base q p s).hom := by
    calc
      (v ≫ t) ≫ T.hom = v ≫ (t ≫ T.hom) := Category.assoc _ _ _
      _ = v ≫ (f ≫ Y.hom) := congrArg (fun z => v ≫ z) ht
      _ = (v ≫ f) ≫ Y.hom := (Category.assoc _ _ _).symm
      _ = (π ≫ h) ≫ Y.hom := congrArg (fun z => z ≫ Y.hom) hw
      _ = π ≫ (h ≫ Y.hom) := Category.assoc _ _ _
      _ = π ≫ (base q p s).hom := congrArg (fun z => π ≫ z) hb
  exact hcalc.trans (Scheme.EtaleChart.retainedToCompactification_fst_assoc
    q.left p.left s.left f j fN hj (base q p s).hom).symm

/-- The fixed-target input f is exactly the original native projection composite. -/
theorem originalTarget_recovery :
    (originalTarget q p s i f hi t ht).left =
      originalSection q p s i f hi ≫ retainedTarget q p s f t :=
  (Scheme.EtaleChart.retainedOriginal_target q.left p.left s.left i f hi t).symm

/-- The fixed-target input g is exactly the original native retract composite. -/
theorem retractTarget_recovery (hs : s.left ≫ p.left = 𝟙 Y.left) :
    (retractTarget q p s i f hi t ht).left =
      retractSection q p s i f hi hs ≫ retainedTarget q p s f t :=
  (Scheme.EtaleChart.retainedRetract_target q.left p.left s.left i f hi t hs).symm

end AlgebraicGeometry.Scheme.SmoothSite.EtaleChart.OriginalFixed
