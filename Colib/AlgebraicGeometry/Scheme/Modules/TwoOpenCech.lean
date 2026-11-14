/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.CechMultifork
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.Stalk

/-!
# The signed Čech short complex of two open subschemes

The middle term is the biproduct of the two actual restriction-direct images.
The differential is first restriction minus second restriction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace

attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] AlgebraicGeometry.Modules.preservesZeroMorphisms_restrictFunctor

namespace CategoryTheory.ShortComplex

/-- The short complex of a commutative square, with a signed second map. -/
def squareComplex {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
    {A B C' D : C} (a : A ⟶ B) (b : A ⟶ C') (c : B ⟶ D) (d : C' ⟶ D)
    (h : a ≫ c = b ≫ d) : ShortComplex C :=
  ShortComplex.mk (biprod.lift a b) (biprod.fst ≫ c - biprod.snd ≫ d) (by
    rw [Preadditive.comp_sub, biprod.lift_fst_assoc, biprod.lift_snd_assoc, h, sub_self])

set_option linter.unusedSimpArgs false in
/-- The signed square complex splits if the left augmentation and opposite edge are invertible. -/
def squareComplex_split_left {C : Type*} [Category* C] [Preadditive C]
    [HasBinaryBiproducts C] {A B C' D : C} (a : A ⟶ B) (b : A ⟶ C')
    (c : B ⟶ D) (d : C' ⟶ D) (h : a ≫ c = b ≫ d) [ha : IsIso a] [hd : IsIso d] :
    (squareComplex a b c d h).Splitting where
  r := (biprod.fst : B ⊞ C' ⟶ B) ≫ @CategoryTheory.inv _ _ _ _ a ha
  s := -(@CategoryTheory.inv _ _ _ _ d hd ≫ biprod.inr)
  f_r := by simp [squareComplex]
  s_g := by simp [squareComplex, Preadditive.comp_sub]
  id := by
    have he : inv a ≫ b = c ≫ inv d := by
      apply (cancel_mono d).1
      simp [Category.assoc, ← h]
    dsimp only [squareComplex, ShortComplex.mk]
    change ((biprod.fst ≫ inv a) ≫ biprod.lift a b) +
        (((biprod.fst : B ⊞ C' ⟶ B) ≫ c - biprod.snd ≫ d) ≫
          (-(inv d ≫ biprod.inr)) : B ⊞ C' ⟶ B ⊞ C') = 𝟙 (B ⊞ C')
    have hr : ((biprod.fst : B ⊞ C' ⟶ B) ≫ inv a) ≫ biprod.lift a b =
        biprod.fst ≫ biprod.inl + biprod.fst ≫ c ≫ inv d ≫ biprod.inr := by
      apply biprod.hom_ext
      · simp [Preadditive.add_comp, Category.assoc]
      · simp [Preadditive.add_comp, Category.assoc, he]
    rw [hr, ← biprod.total]
    simp only [Preadditive.sub_comp, Preadditive.comp_neg, Category.assoc,
      IsIso.hom_inv_id_assoc]
    abel

set_option linter.unusedSimpArgs false in
/-- The signed square complex splits if the right augmentation and opposite edge are invertible. -/
def squareComplex_split_right {C : Type*} [Category* C] [Preadditive C]
    [HasBinaryBiproducts C] {A B C' D : C} (a : A ⟶ B) (b : A ⟶ C')
    (c : B ⟶ D) (d : C' ⟶ D) (h : a ≫ c = b ≫ d) [hb : IsIso b] [hc : IsIso c] :
    (squareComplex a b c d h).Splitting where
  r := (biprod.snd : B ⊞ C' ⟶ C') ≫ @CategoryTheory.inv _ _ _ _ b hb
  s := @CategoryTheory.inv _ _ _ _ c hc ≫ (biprod.inl : B ⟶ B ⊞ C')
  f_r := by simp [squareComplex]
  s_g := by simp [squareComplex, Preadditive.comp_sub]
  id := by
    have he : inv b ≫ a = d ≫ inv c := by
      apply (cancel_mono c).1
      simp [Category.assoc, h]
    dsimp only [squareComplex, ShortComplex.mk]
    change ((biprod.snd ≫ inv b) ≫ biprod.lift a b) +
        (((biprod.fst : B ⊞ C' ⟶ B) ≫ c - biprod.snd ≫ d) ≫
          (inv c ≫ biprod.inl) : B ⊞ C' ⟶ B ⊞ C') = 𝟙 (B ⊞ C')
    have hr : ((biprod.snd : B ⊞ C' ⟶ C') ≫ inv b) ≫ biprod.lift a b =
        biprod.snd ≫ d ≫ inv c ≫ biprod.inl + biprod.snd ≫ biprod.inr := by
      apply biprod.hom_ext
      · simp [Preadditive.add_comp, Category.assoc, he]
      · simp [Preadditive.add_comp, Category.assoc]
    rw [hr, ← biprod.total]
    simp only [Preadditive.sub_comp, Category.assoc, IsIso.hom_inv_id_assoc]
    abel

/-- Additive functors preserve the signed complex of a commutative square. -/
def squareComplexMapIso {C D : Type*} [Category* C] [Category* D] [Preadditive C]
    [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] {A B C' E : C} (a : A ⟶ B) (b : A ⟶ C')
    (c : B ⟶ E) (d : C' ⟶ E) (h : a ≫ c = b ≫ d) :
    (squareComplex a b c d h).map F ≅
      squareComplex (F.map a) (F.map b) (F.map c) (F.map d)
        (by simpa only [← F.map_comp] using congrArg F.map h) := by
  let e : F.obj (B ⊞ C') ≅ F.obj B ⊞ F.obj C' :=
    { hom := biprodComparison F B C'
      inv := biprodComparison' F B C'
      hom_inv_id := by
        rw [biprodComparison, biprodComparison', biprod.lift_desc, ← F.map_comp,
          ← F.map_comp, ← F.map_add, biprod.total, F.map_id]
      inv_hom_id := biprodComparison'_comp_biprodComparison F B C' }
  refine ShortComplex.isoMk (Iso.refl _) e (Iso.refl _) ?_ ?_
  · apply biprod.hom_ext <;>
      simp [e, squareComplex, Category.assoc, ← F.map_comp, biprodComparison_fst,
        biprodComparison_snd]
  · change e.hom ≫ (biprod.fst ≫ F.map c - biprod.snd ≫ F.map d) =
      F.map (biprod.fst ≫ c - biprod.snd ≫ d) ≫ 𝟙 _
    simp only [e, Preadditive.comp_sub, biprodComparison_fst_assoc, biprodComparison_snd_assoc,
      F.map_sub, F.map_comp, Category.comp_id]

end CategoryTheory.ShortComplex

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (U V : X.Opens) (M : X.Modules)

/-- The actual signed Čech short complex for the two opens. -/
def twoOpenCech : ShortComplex X.Modules :=
  ShortComplex.squareComplex
    ((restrictAdjunction U.ι).unit.app M) ((restrictAdjunction V.ι).unit.app M)
    (restrictPushModMap (inf_le_left : U ⊓ V ≤ U) M)
    (restrictPushModMap (inf_le_right : U ⊓ V ≤ V) M)
    (by rw [restrictAdjunction_unit_comp_restrictPushModMap,
      restrictAdjunction_unit_comp_restrictPushModMap])

/-- The signed short complex is exact for every module sheaf on a two-open cover. -/
theorem twoOpenCech_shortExact (hUV : U ⊔ V = ⊤) : (twoOpenCech U V M).ShortExact := by
  let W : ULift.{u} Bool → Scheme.{u} := fun b => if b.down then U.toScheme else V.toScheme
  let j : ∀ b, W b ⟶ X := fun b => by
    rcases b with ⟨b⟩
    cases b with
    | false => exact V.ι
    | true => exact U.ι
  let : ∀ b, IsOpenImmersion (j b) := fun b => by
    rcases b with ⟨b⟩
    cases b <;> dsimp [j] <;> infer_instance
  have hcover : ∀ x : X, ∃ (b : ULift.{u} Bool) (y : W b), j b y = x := by
    intro x
    have hx : x ∈ U ⊔ V := hUV ▸ Set.mem_univ x
    rcases hx with hx | hx
    · exact ⟨⟨true⟩, ⟨x, hx⟩, rfl⟩
    · exact ⟨⟨false⟩, ⟨x, hx⟩, rfl⟩
  apply Stacks.SheafOfModules.shortExact_of_forall_restrict j _ hcover
  let a := (restrictAdjunction U.ι).unit.app M
  let b := (restrictAdjunction V.ι).unit.app M
  let c := restrictPushModMap (inf_le_left : U ⊓ V ≤ U) M
  let d := restrictPushModMap (inf_le_right : U ⊓ V ≤ V) M
  have h : a ≫ c = b ≫ d := by
    dsimp only [a, b, c, d]
    rw [restrictAdjunction_unit_comp_restrictPushModMap,
      restrictAdjunction_unit_comp_restrictPushModMap]
  rintro ⟨t⟩
  cases t with
  | false =>
    let F := restrictFunctor V.ι
    let : F.Additive := Functor.additive_of_iso (restrictFunctorIsoPullback V.ι).symm
    let : IsIso (F.map b) := isIso_restrictFunctor_map_unit V M
    let : IsIso (F.map c) := isIso_restrictFunctor_map_restrictPushModMap
      (inf_le_left : U ⊓ V ≤ U) (le_of_eq (inf_comm V U)) M
    exact ShortComplex.shortExact_of_iso
      (ShortComplex.squareComplexMapIso F a b c d h).symm
      (ShortComplex.squareComplex_split_right _ _ _ _ _).shortExact
  | true =>
    let F := restrictFunctor U.ι
    let : F.Additive := Functor.additive_of_iso (restrictFunctorIsoPullback U.ι).symm
    let : IsIso (F.map a) := isIso_restrictFunctor_map_unit U M
    let : IsIso (F.map d) := isIso_restrictFunctor_map_restrictPushModMap
      (inf_le_right : U ⊓ V ≤ V) le_rfl M
    exact ShortComplex.shortExact_of_iso
      (ShortComplex.squareComplexMapIso F a b c d h).symm
      (ShortComplex.squareComplex_split_left _ _ _ _ _).shortExact

end AlgebraicGeometry.Scheme.Modules
