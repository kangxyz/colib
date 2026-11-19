/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.RepresentedCohomology
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.Indexing
public import Colib.AlgebraicGeometry.Sites.Smooth.FiniteKrullDimension
public import Mathlib.Algebra.Category.Grp.AB

/-!
# The coniveau tower of cohomology with supports

At each codimension bound, take the filtered colimit of cohomology of the
actual open-pair motives. Complementary opens reverse support inclusions,
and contravariant cohomology makes the resulting support diagram covariant.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme Opposite Order TopologicalSpace

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

attribute [local instance] specializationOrder

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "DM(" field ")" => EffectiveMotivesMinus field

variable (X : Sm(k))

/-- Cohomology with the original closed supports and an effective coefficient. -/
def closedSupportCohomology (K : DM(k)) (n : ℤ) : Closeds X.left ⥤ AddCommGrpCat.{w'} :=
  opOp (Closeds X.left) ⋙ (supportOpenPairFunctor k X).op ⋙
    effectivePairCohomology k K n

/-- The support diagram at a fixed codimension bound. -/
abbrev coniveauCohomologyDiagram (K : DM(k)) (n : ℤ) (a : ℕ) :
    ConiveauSupports k X a ⥤ AddCommGrpCat.{w'} :=
  Monotone.functor (f := fun Z ↦ Z.1) (fun _ _ h ↦ h) ⋙ closedSupportCohomology k X K n

/-- The abelian structure for the coefficients in the closed-support stages. -/
local instance coniveauStagesAbelian : Abelian (LargeSheaves k) := SheafWithTransfers.abelian k

variable [UnivLE.{u, w'}]

/-- The coniveau stage is the filtered colimit of cohomology with closed supports. -/
abbrev coniveauCohomology (K : DM(k)) (n : ℤ) (a : ℕ) : AddCommGrpCat.{w'} :=
  colimit (coniveauCohomologyDiagram k X K n a)

set_option maxHeartbeats 550000 in
-- The cocone compares individual maps of restricted support diagrams.
private def coniveauCohomologyTransitionCocone (K : DM(k)) (n : ℤ) {a b : ℕ} (h : a ≤ b) :
    Cocone (coniveauCohomologyDiagram k X K n b) where
  pt := coniveauCohomology k X K n a
  ι := {
    app Z := colimit.ι (coniveauCohomologyDiagram k X K n a)
      ((coniveauSupportsInclusion k X h).obj Z)
    naturality Z W f := by
      let F := coniveauCohomologyDiagram k X K n a
      let I := coniveauSupportsInclusion k X h
      change F.map (I.map f) ≫ colimit.ι F (I.obj W) = colimit.ι F (I.obj Z) ≫ 𝟙 _
      rw [colimit.w, Category.comp_id] }

/-- Forget the larger codimension bound without changing the support class. -/
@[no_expose]
def coniveauCohomologyTransition (K : DM(k)) (n : ℤ) {a b : ℕ} (h : a ≤ b) :
    coniveauCohomology k X K n b ⟶ coniveauCohomology k X K n a :=
  colimit.desc (coniveauCohomologyDiagram k X K n b) (coniveauCohomologyTransitionCocone k X K n h)

set_option maxHeartbeats 550000 in
-- The generator statement retains the concrete support diagrams at both indices.
/-- The transition acts on each support via the native colimit injection. -/
theorem ι_coniveauCohomologyTransition (K : DM(k)) (n : ℤ) {a b : ℕ} (h : a ≤ b)
    (Z : ConiveauSupports k X b) :
    colimit.ι (coniveauCohomologyDiagram k X K n b) Z ≫
        coniveauCohomologyTransition k X K n h =
      colimit.ι (coniveauCohomologyDiagram k X K n a)
        ((coniveauSupportsInclusion k X h).obj Z) := by
  exact colimit.ι_desc (coniveauCohomologyTransitionCocone k X K n h) Z

set_option maxHeartbeats 550000 in
-- The map and its postcomposition have the same literal colimit source.
/-- The generator formula for a support transition followed by a map out of the stage. -/
theorem ι_coniveauCohomologyTransition_assoc (K : DM(k)) (n : ℤ) {a b : ℕ} (h : a ≤ b)
    (Z : ConiveauSupports k X b) {A : AddCommGrpCat.{w'}}
    (m : coniveauCohomology k X K n a ⟶ A) :
    colimit.ι (coniveauCohomologyDiagram k X K n b) Z ≫
        coniveauCohomologyTransition k X K n h ≫ m =
      colimit.ι (coniveauCohomologyDiagram k X K n a)
        ((coniveauSupportsInclusion k X h).obj Z) ≫ m := by
  rw [← Category.assoc, ι_coniveauCohomologyTransition]

set_option maxHeartbeats 800000 in
-- Functoriality uses the colimit injections for three consecutive support bounds.
/-- The transitions give the descending tower indexed by codimension. -/
@[no_expose]
def coniveauCohomologyTower (K : DM(k)) (n : ℤ) : ℕᵒᵖ ⥤ AddCommGrpCat.{w'} where
  obj a := coniveauCohomology k X K n a.unop
  map f := coniveauCohomologyTransition k X K n f.unop.le
  map_id a := by
    apply colimit.hom_ext
    intro Z
    simp only [ι_coniveauCohomologyTransition, Category.comp_id]
    rfl
  map_comp f g := by
    apply colimit.hom_ext
    intro Z
    simp only [← Category.assoc, ι_coniveauCohomologyTransition]
    rfl

set_option maxHeartbeats 800000 in
-- The zero-object calculation uses the abelian structure of transfer sheaves.
set_option synthInstance.maxHeartbeats 100000 in
omit [UnivLE.{u, w'}] in
private theorem isZero_emptySupport_pair :
    IsZero (effectivePairMotive k (supportOpenInclusion k X (⊥ : Closeds X.left))) := by
  have he : (⊥ : Closeds X.left).compl = ⊤ := by
    ext x
    simp [Closeds.compl]
  let j := supportOpenInclusion k X (⊥ : Closeds X.left)
  have hj : IsIso j.left := by
    change IsIso (AlgebraicGeometry.Scheme.Opens.ι (X := X.left) (⊥ : Closeds X.left).compl)
    rw [he]
    exact inferInstanceAs (IsIso X.left.topIso.hom)
  let : IsIso ((SmoothSite.forgetScheme (Spec (.of k))).map j) := hj
  let : IsIso j := isIso_of_reflects_iso j (SmoothSite.forgetScheme (Spec (.of k)))
  let R := smoothTransferRepresentable k
  have : IsIso (R.map j) := Functor.map_isIso R j
  exact (effectiveTransferSheaf k).map_isZero (isZero_cokernel_of_epi (R.map j))

omit [PerfectField k] [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [UnivLE.{u, w'}] in
private theorem coheight_le_topologicalKrullDim (x : X.left) :
    (coheight x : WithBot ℕ∞) ≤ topologicalKrullDim X.left :=
  (coheight_le_krullDim x).trans
    (krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X.left)).symm).le

set_option maxHeartbeats 1000000 in
-- The colimit argument unfolds the shifted Hom of the empty-support motive.
/-- Above a dimension bound every allowed support is empty, so the stage vanishes. -/
theorem isZero_coniveauCohomology_above_dimension (K : DM(k)) (n : ℤ) {d a : ℕ}
    (hX : topologicalKrullDim X.left ≤ d) (hda : d < a) :
    IsZero (coniveauCohomology k X K n a) := by
  have hZ (Z : ConiveauSupports k X a) : Z.1 = ⊥ := by
    apply bot_unique
    intro x hx
    have hd : coheight x ≤ d :=
      WithBot.coe_le_coe.mp ((coheight_le_topologicalKrullDim k X x).trans hX)
    exact False.elim ((ENat.natCast_lt_natCast.mpr hda).not_ge ((Z.2 x hx).trans hd))
  have hzero (Z : ConiveauSupports k X a) :
      IsZero ((coniveauCohomologyDiagram k X K n a).obj Z) := by
    let F := closedSupportCohomology k X K n
    change IsZero (F.obj Z.1)
    rw [hZ Z]
    let H := effectivePairMotive k (supportOpenInclusion k X (⊥ : Closeds X.left)) ⟶ K⟦n⟧
    let : Subsingleton H := ⟨fun f g ↦ (isZero_emptySupport_pair k X).eq_of_src f g⟩
    change IsZero (AddCommGrpCat.of H)
    exact AddCommGrpCat.isZero_of_subsingleton _
  apply (IsZero.iff_id_eq_zero _).2
  apply colimit.hom_ext
  intro Z
  exact (hzero Z).eq_of_src _ _

/-- A smooth finite-type scheme has a finite coniveau tower. -/
theorem exists_isZero_coniveauCohomology (K : DM(k)) (n : ℤ) :
    ∃ d : ℕ, ∀ a > d, IsZero (coniveauCohomology k X K n a) := by
  obtain ⟨d, hd⟩ := SmoothSite.exists_nat_topologicalKrullDim_le k X
  exact ⟨d, fun _ ha ↦ isZero_coniveauCohomology_above_dimension k X K n hd ha⟩

end AlgebraicGeometry.MotivicHomotopy
