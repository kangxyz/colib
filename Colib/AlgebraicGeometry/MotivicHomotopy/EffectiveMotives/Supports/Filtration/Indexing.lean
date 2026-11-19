/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Topology.KrullDimension

/-! # Closed support and nested support diagrams indexed by codimension -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite Order TopologicalSpace AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

attribute [local instance] specializationOrder

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

variable (X : Sm(k))

/-- Closed supports all of whose points have codimension at least `a`. -/
abbrev ConiveauSupports (a : ℕ) :=
  {Z : Closeds X.left // ∀ x : X.left, x ∈ (Z : Set X.left) → (a : ℕ∞) ≤ coheight x}

/-- The empty support is available at every codimension. -/
instance (a : ℕ) : OrderBot (ConiveauSupports k X a) where
  bot := ⟨⊥, fun _ hx ↦ False.elim hx⟩
  bot_le Z := show (⊥ : Closeds X.left) ≤ Z.1 from bot_le

/-- The union of two supports has the same codimension bound. -/
instance (a : ℕ) : SemilatticeSup (ConiveauSupports k X a) :=
  Subtype.semilatticeSup fun _ _ hZ hW x hx ↦ by
    rw [Closeds.coe_sup] at hx
    exact hx.elim (hZ x) (hW x)

/-- Increasing the bound restricts the indexing category of closed supports. -/
def coniveauSupportsInclusion {a b : ℕ} (h : a ≤ b) :
    ConiveauSupports k X b ⥤ ConiveauSupports k X a :=
  Monotone.functor (f := fun Z ↦ ⟨Z.1, fun x hx ↦
    (ENat.natCast_le_natCast.mpr h).trans (Z.2 x hx)⟩) (fun _ _ hZW ↦ hZW)

/-- The complement of a support is included in the original smooth scheme. -/
def supportOpenInclusion (Z : Closeds X.left) :
    (SmoothSite.opensFunctor X).obj Z.compl ⟶ X :=
  SmoothSite.openInclusion X Z.compl

instance (Z : Closeds X.left) :
    IsOpenImmersion (supportOpenInclusion k X Z).left := by
  change IsOpenImmersion (AlgebraicGeometry.Scheme.Opens.ι (X := X.left) Z.compl)
  infer_instance

/-- A larger support has a smaller complementary open. -/
def supportOpenMap {Z W : Closeds X.left} (h : Z ≤ W) :
    (SmoothSite.opensFunctor X).obj W.compl ⟶ (SmoothSite.opensFunctor X).obj Z.compl :=
  (SmoothSite.opensFunctor X).map (homOfLE (Set.compl_subset_compl.mpr h))

instance {Z W : Closeds X.left} (h : Z ≤ W) :
    IsOpenImmersion (supportOpenMap k X h).left := by
  change IsOpenImmersion (X.left.homOfLE (Set.compl_subset_compl.mpr h))
  infer_instance

/-- Complement inclusions commute with the two ambient inclusions. -/
@[reassoc]
theorem supportOpenMap_comp_inclusion {Z W : Closeds X.left} (h : Z ≤ W) :
    supportOpenMap k X h ≫ supportOpenInclusion k X Z = supportOpenInclusion k X W := by
  apply MorphismProperty.Over.Hom.ext
  exact X.left.homOfLE_ι (Set.compl_subset_compl.mpr h)

/-- Successive inclusions of complementary opens compose to the inclusion for the composite. -/
theorem supportOpenMap_comp {Z W V : Closeds X.left} (h : Z ≤ W) (h' : W ≤ V) :
    supportOpenMap k X h' ≫ supportOpenMap k X h = supportOpenMap k X (h.trans h') := by
  apply MorphismProperty.Over.Hom.ext
  exact X.left.homOfLE_homOfLE (Set.compl_subset_compl.mpr h') (Set.compl_subset_compl.mpr h)

/-- The diagram of open pairs associated to closed supports, using identity
on the ambient smooth scheme. -/
def supportOpenPairFunctor : (Closeds X.left)ᵒᵖ ⥤ Arrow Sm(k) where
  obj Z := Arrow.mk (supportOpenInclusion k X Z.unop)
  map f := Arrow.homMk' (supportOpenMap k X f.unop.le) (𝟙 X) (by
    rw [Category.comp_id, supportOpenMap_comp_inclusion])
  map_id Z := by
    apply Arrow.hom_ext
    · exact (SmoothSite.opensFunctor X).map_id _
    · rfl
  map_comp f g := by
    apply Arrow.hom_ext
    · exact (supportOpenMap_comp k X g.unop.le f.unop.le).symm
    · exact (Category.id_comp _).symm

/-- A pair consists of a support of codimension at least `b` contained in
a support of codimension at least `a`. -/
abbrev ConiveauSupportPairs (a b : ℕ) :=
  {ZW : ConiveauSupports k X b × ConiveauSupports k X a // ZW.1.1 ≤ ZW.2.1}

instance (a b : ℕ) : OrderBot (ConiveauSupportPairs k X a b) where
  bot := ⟨(⊥, ⊥), le_rfl⟩
  bot_le ZW := show ((⊥, ⊥) : ConiveauSupports k X b × ConiveauSupports k X a) ≤ ZW.1
    from ⟨bot_le, bot_le⟩

instance (a b : ℕ) : SemilatticeSup (ConiveauSupportPairs k X a b) :=
  Subtype.semilatticeSup fun _ _ hZ hW ↦ sup_le_sup hZ hW

/-- The projection to the smaller support. -/
def coniveauSupportPairsSmall (a b : ℕ) :
    ConiveauSupportPairs k X a b ⥤ ConiveauSupports k X b :=
  Monotone.functor (f := fun ZW ↦ ZW.1.1) (fun _ _ h ↦ h.1)

/-- The projection to the larger support. -/
def coniveauSupportPairsLarge (a b : ℕ) :
    ConiveauSupportPairs k X a b ⥤ ConiveauSupports k X a :=
  Monotone.functor (f := fun ZW ↦ ZW.1.2) (fun _ _ h ↦ h.2)

/-- When the smaller support has the stronger bound, every such support occurs
as a first coordinate by pairing it with itself. -/
theorem coniveauSupportPairsSmall_final {a b : ℕ} (hab : a ≤ b) :
    (coniveauSupportPairsSmall k X a b).Final := by
  have hf : Monotone (fun ZW : ConiveauSupportPairs k X a b ↦ ZW.1.1) := by
    intro ZW ZW' h
    exact (show ZW.1 ≤ ZW'.1 from h).1
  apply (Monotone.final_functor_iff hf).2
  intro Z
  exact ⟨⟨(Z, (coniveauSupportsInclusion k X hab).obj Z), le_rfl⟩, le_rfl⟩

instance (a b : ℕ) : (coniveauSupportPairsLarge k X a b).Final := by
  have hf : Monotone (fun ZW : ConiveauSupportPairs k X a b ↦ ZW.1.2) := by
    intro ZW ZW' h
    exact (show ZW.1 ≤ ZW'.1 from h).2
  apply (Monotone.final_functor_iff hf).2
  intro W
  exact ⟨⟨(⊥, W), (show (⊥ : Closeds X.left) ≤ W.1 from bot_le)⟩, le_rfl⟩

/-- The original nested complementary opens as a diagram of arrows. -/
def coniveauSupportPairsInclusion (a b : ℕ) :
    (ConiveauSupportPairs k X a b)ᵒᵖ ⥤ Arrow Sm(k) where
  obj ZW := Arrow.mk (supportOpenMap k X ZW.unop.2)
  map f := Arrow.homMk' (supportOpenMap k X f.unop.le.2)
    (supportOpenMap k X f.unop.le.1) (by rw [supportOpenMap_comp, supportOpenMap_comp])
  map_id ZW := by
    apply Arrow.hom_ext
    · exact (SmoothSite.opensFunctor X).map_id _
    · exact (SmoothSite.opensFunctor X).map_id _
  map_comp f g := by
    apply Arrow.hom_ext
    · exact (supportOpenMap_comp k X g.unop.le.2 f.unop.le.2).symm
    · exact (supportOpenMap_comp k X g.unop.le.1 f.unop.le.1).symm

end AlgebraicGeometry.MotivicHomotopy
