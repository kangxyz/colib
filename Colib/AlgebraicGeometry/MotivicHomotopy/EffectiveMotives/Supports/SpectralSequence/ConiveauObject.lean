/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.SpectralSequence.ClosedSupports
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.SpectralSequence.WindowColimits.SpectralObject

/-!
# The coniveau spectral object

The spectral object of the codimension filtration has window groups given by
the relative cohomology of original complementary open pairs. Its boundary
on a flag of supports is the corresponding localization boundary.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open Opposite OrderDual AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

section DiagramComparison

variable {I J C : Type*} [Category I] [Category J] [Category C]
  [HasColimitsOfShape I C] [HasColimitsOfShape J C]

private abbrev colimitIsoOfEq {F G : I ⥤ C} (h : F = G) : colimit F ≅ colimit G :=
  eqToIso (congrArg (fun L : I ⥤ C ↦ colimit L) h)

private theorem ι_colimitIsoOfEq_hom {F G : I ⥤ C} (h : F = G) (i : I) :
    colimit.ι F i ≫ (colimitIsoOfEq h).hom =
      eqToHom (Functor.congr_obj h i) ≫ colimit.ι G i := by
  cases h
  simp

private theorem ι_colimitIsoOfEq_inv {F G : I ⥤ C} (h : F = G) (i : I) :
    colimit.ι G i ≫ (colimitIsoOfEq h).inv =
      eqToHom (Functor.congr_obj h.symm i) ≫ colimit.ι F i := by
  cases h
  simp

private theorem colimitIsoOfEq_naturality {F G : I ⥤ C} {F' G' : J ⥤ C}
    (h : F = G) (h' : F' = G') (p : I → J)
    (f : colimit F ⟶ colimit F') (g : colimit G ⟶ colimit G')
    (hf : ∀ i, HEq (colimit.ι F i ≫ f) (colimit.ι F' (p i)))
    (hg : ∀ i, HEq (colimit.ι G i ≫ g) (colimit.ι G' (p i))) :
    f ≫ (colimitIsoOfEq h').hom = (colimitIsoOfEq h).hom ≫ g := by
  cases h
  cases h'
  simp only [colimitIsoOfEq, eqToIso_refl, Iso.refl_hom,
    Category.comp_id, Category.id_comp]
  exact colimit.hom_ext fun i ↦ (hf i).trans (hg i).symm |>.eq

private theorem ι_conj_colimitIsoOfEq {F G : I ⥤ C} {F' G' : J ⥤ C}
    (h : F = G) (h' : F' = G') (i : I) (j : J) (f : colimit F ⟶ colimit F')
    (φ : F.obj i ⟶ F'.obj j) (ψ : G.obj i ⟶ G'.obj j)
    (hφ : HEq φ ψ) (hf : colimit.ι F i ≫ f = φ ≫ colimit.ι F' j) :
    colimit.ι G i ≫ (colimitIsoOfEq h).inv ≫ f ≫ (colimitIsoOfEq h').hom =
      ψ ≫ colimit.ι G' j := by
  cases h
  cases h'
  simpa only [colimitIsoOfEq, eqToIso_refl, Iso.refl_inv, Iso.refl_hom,
    Category.comp_id, Category.id_comp, hφ.eq] using hf

end DiagramComparison

variable (k : Type u) [Field k]
  (X : SmoothSite (Spec (CommRingCat.of k)))

set_option maxHeartbeats 550000 in
-- Compare the original pairs and their squares before applying represented cohomology.
private theorem coniveauWindowOpenPairs_eq (a b : ℕ) :
    coniveauSupportPairsToArrows k X a b ⋙ closedSupportOpenPairs k X =
      opOp (ConiveauSupportPairs k X a b) ⋙ (coniveauSupportPairsInclusion k X a b).op :=
  rfl

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [UnivLE.{u, w'}]
  (K : EffectiveMotivesMinus k)

attribute [local irreducible] Cor.graphFunctor SheafWithTransfers.transferRepresentable

local notation "S" => closedSupportSpectralObject k X K
local notation "D" => closedSupportWindowDiagram k X S
local notation "W" => coniveauRelativeSupportDiagram k X K

/-- The spectral object of the coniveau filtration with coefficients in an effective motive. -/
def coniveauSpectralObject : Abelian.SpectralObject AddCommGrpCat.{w'} ℕᵒᵈ :=
  closedSupportWindowSpectralObject k X S

section WindowComparison

attribute [local irreducible] effectivePairCohomology

set_option maxHeartbeats 550000 in
-- The pair comparison is transported by the opaque represented cohomology functor.
omit [UnivLE.{u, w'}] in
private theorem coniveauWindowDiagram_eq (n : ℤ) (a b : ℕ) : D n a b = W n a b :=
  let F := coniveauSupportPairsToArrows k X a b
  let H := effectivePairCohomology k K n
  (congrArg (F ⋙ ·) (closedSupportSpectralObject_H k X K n)).trans
    (congrArg (· ⋙ H) (coniveauWindowOpenPairs_eq k X a b))

end WindowComparison

/-- Evaluation on `b ⟶ a` gives the relative coniveau cohomology between the two bounds. -/
@[no_expose]
def coniveauSpectralObjectWindowIso (n : ℤ) (a b : ℕ) (hab : a ≤ b) :
    ((coniveauSpectralObject k X K).H n).obj
      (mk₁ (homOfLE (show toDual b ≤ toDual a from hab))) ≅
        coniveauRelativeSupportCohomology k X K n a b :=
  colimitIsoOfEq (coniveauWindowDiagram_eq k X K n a b)

set_option maxHeartbeats 750000 in
-- The source of the cocone injection is the original pair cohomology.
/-- The window comparison identifies the same relative cohomology generator. -/
theorem ι_coniveauSpectralObjectWindowIso_hom (n : ℤ) {a b : ℕ} (hab : a ≤ b)
    (T : ConiveauSupportPairs k X a b) :
    colimit.ι (D n a b) T ≫ (coniveauSpectralObjectWindowIso k X K n a b hab).hom =
      colimit.ι (W n a b) T := by
  have h := ι_colimitIsoOfEq_hom (coniveauWindowDiagram_eq k X K n a b) T
  have hi : eqToHom (Functor.congr_obj (coniveauWindowDiagram_eq k X K n a b) T) =
      𝟙 ((W n a b).obj T) := rfl
  exact h.trans ((congrArg (· ≫ colimit.ι (W n a b) T) hi).trans (Category.id_comp _))

set_option maxHeartbeats 750000 in
-- The inverse comparison is checked on the literal window injections.
/-- The inverse window comparison identifies the same relative cohomology generator. -/
theorem ι_coniveauSpectralObjectWindowIso_inv (n : ℤ) {a b : ℕ} (hab : a ≤ b)
    (T : ConiveauSupportPairs k X a b) :
    colimit.ι (W n a b) T ≫ (coniveauSpectralObjectWindowIso k X K n a b hab).inv =
      colimit.ι (D n a b) T := by
  have h := ι_colimitIsoOfEq_inv (coniveauWindowDiagram_eq k X K n a b) T
  have hi : eqToHom (Functor.congr_obj (coniveauWindowDiagram_eq k X K n a b).symm T) =
      𝟙 ((D n a b).obj T) := rfl
  exact h.trans ((congrArg (· ≫ colimit.ι (D n a b) T) hi).trans (Category.id_comp _))

set_option maxHeartbeats 750000 in
-- The typed generator equations identify the comparison on the two index categories.
/-- Under the window comparison the spectral-object map simply weakens both bounds. -/
theorem coniveauSpectralObjectWindowIso_naturality (n : ℤ)
    {a b a' b' : ℕ} (hab : a ≤ b) (hab' : a' ≤ b')
    (f : mk₁ (homOfLE (show toDual b ≤ toDual a from hab)) ⟶
      mk₁ (homOfLE (show toDual b' ≤ toDual a' from hab'))) :
    ((coniveauSpectralObject k X K).H n).map f ≫
        (coniveauSpectralObjectWindowIso k X K n a' b' hab').hom =
      (coniveauSpectralObjectWindowIso k X K n a b hab).hom ≫
        coniveauWindowMap k X K n (f.app 1).le (f.app 0).le :=
  colimitIsoOfEq_naturality (coniveauWindowDiagram_eq k X K n a b)
    (coniveauWindowDiagram_eq k X K n a' b')
    (coniveauSupportPairsWeaken k X (f.app 1).le (f.app 0).le).obj
    ((closedSupportWindowFunctor k X S n).map f)
    (coniveauWindowMap k X K n (f.app 1).le (f.app 0).le)
    (fun T ↦ heq_of_eq (ι_closedSupportWindowFunctor_map k X S n f T))
    (fun T ↦ heq_of_eq (ι_coniveauWindowMap k X K n (f.app 1).le (f.app 0).le T))

/-- The connecting map from the window `(a,b)` to the window `(b,c)` in the next degree. -/
def coniveauWindowConnecting (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    coniveauRelativeSupportCohomology k X K n₀ a b ⟶
      coniveauRelativeSupportCohomology k X K n₁ b c :=
  (coniveauSpectralObjectWindowIso k X K n₀ a b hab).inv ≫
    (coniveauSpectralObject k X K).δ
      (homOfLE (show toDual c ≤ toDual b from hbc))
      (homOfLE (show toDual b ≤ toDual a from hab)) n₀ n₁ hn₁ ≫
    (coniveauSpectralObjectWindowIso k X K n₁ b c hbc).hom

/-- The window comparison intertwines the two presentations of the connecting map. -/
theorem coniveauSpectralObject_δ_windowIso (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (coniveauSpectralObject k X K).δ
      (homOfLE (show toDual c ≤ toDual b from hbc))
      (homOfLE (show toDual b ≤ toDual a from hab)) n₀ n₁ hn₁ ≫
        (coniveauSpectralObjectWindowIso k X K n₁ b c hbc).hom =
      (coniveauSpectralObjectWindowIso k X K n₀ a b hab).hom ≫
        coniveauWindowConnecting k X K n₀ n₁ hn₁ hab hbc := by
  simp only [coniveauWindowConnecting, Iso.hom_inv_id_assoc]

set_option maxHeartbeats 750000 in
-- The source and target generators come from the two original diagrams.
/-- The window connecting map carries a generator by the signed boundary on its flag. -/
theorem ι_coniveauWindowConnecting (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (T : ConiveauSupportTriples k X a b c) :
    colimit.ι (W n₀ a b) ((coniveauSupportTriplesRight k X a b c).obj T) ≫
        coniveauWindowConnecting k X K n₀ n₁ hn₁ hab hbc =
      (S).δ (homOfLE T.small_le_middle) (homOfLE T.middle_le_large) n₀ n₁ hn₁ ≫
        colimit.ι (W n₁ b c) ((coniveauSupportTriplesLeft k X a b c).obj T) :=
  let d := (coniveauSpectralObject k X K).δ
    (homOfLE (show toDual c ≤ toDual b from hbc))
    (homOfLE (show toDual b ≤ toDual a from hab)) n₀ n₁ hn₁
  let δ := (S).δ (homOfLE T.small_le_middle) (homOfLE T.middle_le_large) n₀ n₁ hn₁
  ι_conj_colimitIsoOfEq (coniveauWindowDiagram_eq k X K n₀ a b)
    (coniveauWindowDiagram_eq k X K n₁ b c)
    ((coniveauSupportTriplesRight k X a b c).obj T)
    ((coniveauSupportTriplesLeft k X a b c).obj T) d δ δ HEq.rfl
    (ι_closedSupportWindowSpectralObject_δ k X S n₀ n₁ hn₁ hab hbc T)

end AlgebraicGeometry.MotivicHomotopy
