/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.WindowData

/-!
# Indexing coniveau windows and flags

A coniveau window is indexed by nested supports. Forgetting any one support in a
flag with ordered codimension bounds is final in the corresponding window index.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]
  (X : SmoothSite (Spec (CommRingCat.of k)))

/-- Weaken both codimension bounds while keeping the two supports. -/
def coniveauSupportPairsWeaken {a b a' b' : ℕ} (ha : a' ≤ a) (hb : b' ≤ b) :
    ConiveauSupportPairs k X a b ⥤ ConiveauSupportPairs k X a' b' :=
  Monotone.functor (f := fun T ↦
    ⟨((coniveauSupportsInclusion k X hb).obj T.1.1,
      (coniveauSupportsInclusion k X ha).obj T.1.2), T.2⟩) fun _ _ h ↦ h

/-- Three nested closed supports, in order of decreasing codimension bound. -/
abbrev ConiveauSupportTriples (a b c : ℕ) :=
  {T : ConiveauSupports k X c × ConiveauSupports k X b × ConiveauSupports k X a //
    T.1.1 ≤ T.2.1.1 ∧ T.2.1.1 ≤ T.2.2.1}

namespace ConiveauSupportTriples

variable {k X} {a b c : ℕ}

/-- The smallest support of a flag, with codimension bound `c`. -/
abbrev small (T : ConiveauSupportTriples k X a b c) := T.1.1

/-- The middle support of a flag, with codimension bound `b`. -/
abbrev middle (T : ConiveauSupportTriples k X a b c) := T.1.2.1

/-- The largest support of a flag, with codimension bound `a`. -/
abbrev large (T : ConiveauSupportTriples k X a b c) := T.1.2.2

/-- The inclusion from the smallest to the middle support. -/
theorem small_le_middle (T : ConiveauSupportTriples k X a b c) :
    T.small.1 ≤ T.middle.1 := T.2.1

/-- The inclusion from the middle to the largest support. -/
theorem middle_le_large (T : ConiveauSupportTriples k X a b c) :
    T.middle.1 ≤ T.large.1 := T.2.2

end ConiveauSupportTriples

instance (a b c : ℕ) : OrderBot (ConiveauSupportTriples k X a b c) where
  bot := ⟨(⊥, ⊥, ⊥), le_rfl, le_rfl⟩
  bot_le T := show (⊥, ⊥, ⊥) ≤ T.1 from ⟨bot_le, bot_le, bot_le⟩

instance (a b c : ℕ) : SemilatticeSup (ConiveauSupportTriples k X a b c) :=
  Subtype.semilatticeSup fun _ _ hT hT' ↦
    ⟨sup_le_sup hT.1 hT'.1, sup_le_sup hT.2 hT'.2⟩

/-- The pair of the smallest and the middle support. -/
def coniveauSupportTriplesLeft (a b c : ℕ) :
    ConiveauSupportTriples k X a b c ⥤ ConiveauSupportPairs k X b c :=
  Monotone.functor (f := fun T ↦ ⟨(T.small, T.middle), T.small_le_middle⟩)
    fun _ _ h ↦ ⟨h.1, h.2.1⟩

/-- The pair of the smallest and the largest support. -/
def coniveauSupportTriplesMiddle (a b c : ℕ) :
    ConiveauSupportTriples k X a b c ⥤ ConiveauSupportPairs k X a c :=
  Monotone.functor (f := fun T ↦
    ⟨(T.small, T.large), T.small_le_middle.trans T.middle_le_large⟩)
    fun _ _ h ↦ ⟨h.1, h.2.2⟩

/-- The pair of the middle and the largest support. -/
def coniveauSupportTriplesRight (a b c : ℕ) :
    ConiveauSupportTriples k X a b c ⥤ ConiveauSupportPairs k X a b :=
  Monotone.functor (f := fun T ↦ ⟨(T.middle, T.large), T.middle_le_large⟩)
    fun _ _ h ↦ h.2

/-- Extend a pair by repeating its larger support with the weaker bound. -/
theorem coniveauSupportTriplesLeft_final {a b c : ℕ} (hab : a ≤ b) :
    (coniveauSupportTriplesLeft k X a b c).Final := by
  have hf : Monotone (fun T : ConiveauSupportTriples k X a b c ↦
      (⟨(T.small, T.middle), T.small_le_middle⟩ : ConiveauSupportPairs k X b c)) :=
    fun _ _ h ↦ ⟨h.1, h.2.1⟩
  apply (Monotone.final_functor_iff hf).2
  intro ZW
  exact ⟨⟨(ZW.1.1, ZW.1.2, (coniveauSupportsInclusion k X hab).obj ZW.1.2),
    ZW.2, le_rfl⟩, le_rfl⟩

/-- Extend a pair to a flag by inserting its smaller support with the weaker bound. -/
theorem coniveauSupportTriplesMiddle_final {a b c : ℕ} (hbc : b ≤ c) :
    (coniveauSupportTriplesMiddle k X a b c).Final := by
  have hf : Monotone (fun T : ConiveauSupportTriples k X a b c ↦
      (⟨(T.small, T.large), T.small_le_middle.trans T.middle_le_large⟩ :
        ConiveauSupportPairs k X a c)) :=
    fun _ _ h ↦ ⟨h.1, h.2.2⟩
  apply (Monotone.final_functor_iff hf).2
  intro ZW
  exact ⟨⟨(ZW.1.1, (coniveauSupportsInclusion k X hbc).obj ZW.1.1, ZW.1.2),
    le_rfl, ZW.2⟩, le_rfl⟩

/-- Extend a pair by placing the empty support in the smallest position. -/
instance (a b c : ℕ) : (coniveauSupportTriplesRight k X a b c).Final := by
  have hf : Monotone (fun T : ConiveauSupportTriples k X a b c ↦
      (⟨(T.middle, T.large), T.middle_le_large⟩ : ConiveauSupportPairs k X a b)) :=
    fun _ _ h ↦ h.2
  apply (Monotone.final_functor_iff hf).2
  intro ZW
  exact ⟨⟨(⊥, ZW.1.1, ZW.1.2), bot_le, ZW.2⟩, le_rfl⟩

/-- Weaken the bounds of a flag without changing its closed supports. -/
def coniveauSupportTriplesWeaken {a b c a' b' c' : ℕ}
    (ha : a' ≤ a) (hb : b' ≤ b) (hc : c' ≤ c) (T : ConiveauSupportTriples k X a b c) :
    ConiveauSupportTriples k X a' b' c' :=
  ⟨((coniveauSupportsInclusion k X hc).obj T.small,
    (coniveauSupportsInclusion k X hb).obj T.middle,
    (coniveauSupportsInclusion k X ha).obj T.large), T.small_le_middle, T.middle_le_large⟩

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [UnivLE.{u, w'}]

attribute [local irreducible] effectivePairCohomology

set_option maxHeartbeats 550000 in
-- The two indexing objects have the same complementary opens.
/-- The colimit injection at the weakened pair, viewed from the original pair cohomology. -/
def coniveauWindowMapGenerator (K : EffectiveMotivesMinus k) (n : ℤ)
    {a b a' b' : ℕ} (ha : a' ≤ a) (hb : b' ≤ b) (T : ConiveauSupportPairs k X a b) :
    (coniveauRelativeSupportDiagram k X K n a b).obj T ⟶
      coniveauRelativeSupportCohomology k X K n a' b' :=
  colimit.ι (coniveauRelativeSupportDiagram k X K n a' b')
    ((coniveauSupportPairsWeaken k X ha hb).obj T)

set_option maxHeartbeats 550000 in
-- Check naturality on the unchanged pair of opens for each support inclusion.
private def coniveauWindowMapCocone (K : EffectiveMotivesMinus k) (n : ℤ)
    {a b a' b' : ℕ} (ha : a' ≤ a) (hb : b' ≤ b) :
    Cocone (coniveauRelativeSupportDiagram k X K n a b) where
  pt := coniveauRelativeSupportCohomology k X K n a' b'
  ι :=
    { app := coniveauWindowMapGenerator k X K n ha hb
      naturality T U f := by
        let F := coniveauRelativeSupportDiagram k X K n a' b'
        let P := coniveauSupportPairsWeaken k X ha hb
        change F.map (P.map f) ≫ colimit.ι F (P.obj U) = colimit.ι F (P.obj T) ≫ 𝟙 _
        rw [colimit.w, Category.comp_id] }

/-- The coniveau window map given by weakening its two bounds. -/
@[no_expose]
def coniveauWindowMap (K : EffectiveMotivesMinus k) (n : ℤ)
    {a b a' b' : ℕ} (ha : a' ≤ a) (hb : b' ≤ b) :
    coniveauRelativeSupportCohomology k X K n a b ⟶
      coniveauRelativeSupportCohomology k X K n a' b' :=
  colimit.desc (coniveauRelativeSupportDiagram k X K n a b)
    (coniveauWindowMapCocone k X K n ha hb)

set_option maxHeartbeats 550000 in
-- The generator statement uses the literal window diagrams at both sets of bounds.
/-- The window map takes each generator to the generator on the same pair of closed supports. -/
theorem ι_coniveauWindowMap (K : EffectiveMotivesMinus k) (n : ℤ)
    {a b a' b' : ℕ} (ha : a' ≤ a) (hb : b' ≤ b) (T : ConiveauSupportPairs k X a b) :
    colimit.ι (coniveauRelativeSupportDiagram k X K n a b) T ≫ coniveauWindowMap k X K n ha hb =
      coniveauWindowMapGenerator k X K n ha hb T :=
  colimit.ι_desc (coniveauWindowMapCocone k X K n ha hb) T

end AlgebraicGeometry.MotivicHomotopy
