/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Monoidal.Stages

/-! # Coherence of tensor comparisons for iterated twists

The comparison that collects twists is compatible with the associator,
unitors and symmetry. The proofs append one twist at a time. Appending in
each of the three input positions reduces associator compatibility to a
separate equation of associators and braidings.
-/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Stabilization

open MonoidalCategory BraidedCategory
open scoped MonoidalCategory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (L : C)

local notation "T" => tensorRight L
local notation "I" => iterateTensorObj L
local notation "P" => iterateTensorIso L
local notation "l" => moveTensorLeft L
local notation "r" => moveTensorRight L
local notation "ι" => eqToHom

section
variable [BraidedCategory C]

@[reassoc]
private lemma left_succ (hL : (β_ L L).hom = 𝟙 _) (A B : C) (p q : ℕ) :
    (P A B (p + 1) q).hom = (l (I p A) (I q B)).hom ≫ (P A B p q).hom ▷ L ≫
      ι (congrArg (fun k => I k (A ⊗ B)) (Nat.succ_add p q).symm) := by
  rw [iterateTensorIso_left_succ L hL]
  rfl

@[reassoc]
private lemma right_succ (A B : C) (p q : ℕ) :
    (P A B p (q + 1)).hom = (r (I p A) (I q B)).hom ≫ (P A B p q).hom ▷ L := rfl

omit [BraidedCategory C] in
private lemma iter_map_succ {A B : C} (f : A ⟶ B) (p : ℕ) :
    (iterate T (p + 1)).map f = (iterate T p).map f ▷ L := rfl

private lemma normalize_left_zero (A B : C) : (P A B 0 0).hom = 𝟙 (A ⊗ B) := rfl

omit [BraidedCategory C] in
private lemma iterateTensorObj_succ (A : C) (p : ℕ) : I (p + 1) A = I p A ⊗ L := rfl

omit [BraidedCategory C] in
private lemma iterateTensorObj_zero (A : C) : I 0 A = A := rfl

omit [BraidedCategory C] in
private lemma leftUnitor_aux (B : C) :
    (r (𝟙_ C) B).hom ≫ (λ_ B).hom ▷ L = (λ_ (B ⊗ L)).hom := by
  dsimp only [moveTensorRight, Iso.symm_hom]
  monoidal

private lemma rightUnitor_aux (A : C) :
    (l A (𝟙_ C)).hom ≫ (ρ_ A).hom ▷ L = (ρ_ (A ⊗ L)).hom := by
  simp only [moveTensorLeft, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
    show (β_ L (𝟙_ C)).hom = (ρ_ L).hom ≫ (λ_ L).inv from by
      rw [← braiding_leftUnitor L, Category.assoc, Iso.hom_inv_id, Category.comp_id],
    whiskerLeft_comp]
  monoidal

/-- The shuffle identifies the iterated left unitor with the left unitor of the realization. -/
lemma iterateTensorIso_leftUnitor (A : C) (p : ℕ) :
    (P (𝟙_ C) A 0 p).hom ≫ (iterate T (0 + p)).map (λ_ A).hom ≫
      ι (congrArg (fun k => I k A) (Nat.zero_add p)) =
      (λ_ (I p A)).hom := by
  induction p with
  | zero => change 𝟙 _ ≫ (λ_ A).hom ≫ 𝟙 _ = (λ_ A).hom; simp
  | succ p ih =>
      simp only [right_succ, Category.assoc]
      have he : ι (congrArg (fun k => I k A) (Nat.zero_add (p + 1))) =
          (ι (congrArg (fun k => I k A) (Nat.zero_add p)) ▷ L) := by
        rw [eqToHom_whiskerRight]
      rw [he]
      change (r (𝟙_ C) (I p A)).hom ≫ (P (𝟙_ C) A 0 p).hom ▷ L ≫
        (iterate T (0 + p)).map (λ_ A).hom ▷ L ≫
        (ι (congrArg (fun k => I k A) (Nat.zero_add p)) ▷ L) =
        (λ_ (I p A ⊗ L)).hom
      rw [← comp_whiskerRight, ← comp_whiskerRight, ih]
      exact leftUnitor_aux L (I p A)

/-- The shuffle identifies the iterated right unitor with the right unitor of the realization. -/
lemma iterateTensorIso_rightUnitor (hL : (β_ L L).hom = 𝟙 _) (A : C) (p : ℕ) :
    (P A (𝟙_ C) p 0).hom ≫ (iterate T p).map (ρ_ A).hom =
      (ρ_ (I p A)).hom := by
  induction p with
  | zero => change 𝟙 _ ≫ (ρ_ A).hom = (ρ_ A).hom; simp
  | succ p ih =>
      simp only [left_succ L hL, iter_map_succ, eqToHom_refl, Category.id_comp, Category.assoc]
      rw [← comp_whiskerRight, ih]
      exact rightUnitor_aux L (I p A)

end

section
variable [SymmetricCategory C]

@[reassoc]
private lemma braid_aux (A B : C) :
    (r A B).hom ≫ (β_ A B).hom ▷ L = (β_ A (B ⊗ L)).hom ≫ (l B A).hom := by
  simp only [moveTensorRight, moveTensorLeft, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, braiding_tensor_right_hom, Category.assoc, Iso.inv_hom_id_assoc,
    ← whiskerLeft_comp_assoc, SymmetricCategory.symmetry, whiskerLeft_id, Category.id_comp,
    Iso.hom_inv_id, Category.comp_id]

@[reassoc]
private lemma braid_aux_left (A B : C) :
    (l A B).hom ≫ (β_ A B).hom ▷ L = (β_ (A ⊗ L) B).hom ≫ (r B A).hom := by
  simp only [moveTensorRight, moveTensorLeft, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, braiding_tensor_left_hom, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The shuffle identifies the iterated braiding with the braiding of the realizations. -/
lemma iterateTensorIso_braiding (hL : (β_ L L).hom = 𝟙 _) (A B : C) (p q : ℕ) :
    (P A B p q).hom ≫ (iterate T (p + q)).map (β_ A B).hom ≫
      ι (congrArg (fun k => I k (B ⊗ A)) (Nat.add_comm p q)) =
      (β_ (I p A) (I q B)).hom ≫ (P B A q p).hom := by
  induction q with
  | zero =>
      induction p with
      | zero => change 𝟙 _ ≫ (β_ A B).hom ≫ 𝟙 _ = (β_ A B).hom ≫ 𝟙 _; simp
      | succ p ih =>
          have he : ι (congrArg (fun k => I k (B ⊗ A)) (Nat.add_comm (p + 1) 0)) =
              (ι (congrArg (fun k => I k (B ⊗ A)) (Nat.add_comm p 0)) ▷ L) := by
            rw [eqToHom_whiskerRight]
          simp only [left_succ L hL A B p 0, right_succ, eqToHom_refl, Category.id_comp,
            Category.assoc]
          rw [he]
          change (l (I p A) B).hom ≫ (P A B p 0).hom ▷ L ≫
              (iterate T (p + 0)).map (β_ A B).hom ▷ L ≫
              (ι (congrArg (fun k => I k (B ⊗ A)) (Nat.add_comm p 0)) ▷ L) =
            (β_ (I p A ⊗ L) B).hom ≫ (r B (I p A)).hom ≫ (P B A 0 p).hom ▷ L
          rw [← comp_whiskerRight, ← comp_whiskerRight, ih, comp_whiskerRight]
          change (l (I p A) B).hom ≫ (β_ (I p A) B).hom ▷ L ≫ _ =
            (β_ (I p A ⊗ L) B).hom ≫ (r B (I p A)).hom ≫ _
          rw [braid_aux_left_assoc]
  | succ q ih =>
      have h := congrArg (fun k => I k (B ⊗ A)) (Nat.add_comm p q)
      have he : ι (congrArg (fun k => I k (B ⊗ A)) (Nat.add_comm p (q + 1))) =
          (ι h ▷ L) ≫ ι (congrArg (fun k => I k (B ⊗ A)) (Nat.succ_add q p).symm) := by
        rw [eqToHom_whiskerRight, eqToHom_trans]
      simp only [right_succ, left_succ L hL B A q p, Category.assoc]
      rw [he]
      change (r (I p A) (I q B)).hom ≫ (P A B p q).hom ▷ L ≫
          (iterate T (p + q)).map (β_ A B).hom ▷ L ≫
          (ι h ▷ L) ≫ _ = (β_ (I p A) (I q B ⊗ L)).hom ≫ _
      rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc,
        Category.assoc (P A B p q).hom ((iterate T (p + q)).map (β_ A B).hom) (ι h)]
      rw [show (P A B p q).hom ≫ (iterate T (p + q)).map (β_ A B).hom ≫ ι h =
        (β_ (I p A) (I q B)).hom ≫ (P B A q p).hom from ih]
      rw [comp_whiskerRight, Category.assoc, braid_aux_assoc]

end


section
variable [BraidedCategory C]

omit [BraidedCategory C] in
@[reassoc]
private lemma assoc_right_step (A B D : C) :
    (r (A ⊗ B) D).hom ≫ (α_ A B D).hom ▷ L =
      (α_ A B (D ⊗ L)).hom ≫ (A ◁ (r B D).hom) ≫ (r A (B ⊗ D)).hom := by
  dsimp only [moveTensorRight, Iso.symm_hom]
  monoidal

@[reassoc]
private lemma moveTensorLeft_natural_first {A A' : C} (f : A ⟶ A') (D : C) :
    (f ▷ L) ▷ D ≫ (l A' D).hom = (l A D).hom ≫ (f ▷ D) ▷ L := by
  simp only [moveTensorLeft, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, associator_inv_naturality_left]

@[reassoc]
private lemma assoc_middle_step (A B D : C) :
    (r A B).hom ▷ D ≫ (l (A ⊗ B) D).hom ≫ (α_ A B D).hom ▷ L =
      (α_ A (B ⊗ L) D).hom ≫ (A ◁ (l B D).hom) ≫ (r A (B ⊗ D)).hom := by
  simp only [moveTensorLeft, moveTensorRight, Iso.symm_hom, Iso.trans_hom, whiskerLeftIso_hom]
  monoidal

@[reassoc]
private lemma assoc_left_step (A B D : C) :
    (l A B).hom ▷ D ≫ (l (A ⊗ B) D).hom ≫ (α_ A B D).hom ▷ L =
      (α_ (A ⊗ L) B D).hom ≫ (l A (B ⊗ D)).hom := by
  simp only [moveTensorLeft, Iso.symm_hom, Iso.trans_hom, whiskerLeftIso_hom,
    braiding_tensor_right_hom, whiskerLeft_comp]
  monoidal

/-- The shuffle identifies the iterated associator with the associator of the realizations. -/
lemma iterateTensorIso_associator (hL : (β_ L L).hom = 𝟙 _) (A B D : C) (p q r₀ : ℕ) :
    (P A B p q).hom ▷ I r₀ D ≫ (P (A ⊗ B) D (p + q) r₀).hom ≫
        (iterate T ((p + q) + r₀)).map (α_ A B D).hom ≫
        ι (congrArg (fun k => I k (A ⊗ B ⊗ D)) (Nat.add_assoc p q r₀)) =
      (α_ (I p A) (I q B) (I r₀ D)).hom ≫
        (I p A ◁ (P B D q r₀).hom) ≫ (P A (B ⊗ D) p (q + r₀)).hom := by
  induction r₀ with
  | zero =>
      induction q with
      | zero =>
          induction p with
          | zero =>
              change 𝟙 _ ▷ D ≫ 𝟙 _ ≫ (α_ A B D).hom ≫ 𝟙 _ =
                (α_ A B D).hom ≫ (A ◁ 𝟙 _) ≫ 𝟙 _
              simp
          | succ p ih =>
              simp only [left_succ L hL, eqToHom_refl, Category.comp_id, normalize_left_zero,
                comp_whiskerRight, Category.assoc]
              have ih' : (P A B p 0).hom ▷ D ≫ (P (A ⊗ B) D p 0).hom ≫
                    (iterate T p).map (α_ A B D).hom =
                  (α_ (I p A) B D).hom ≫ (P A (B ⊗ D) p 0).hom := by
                simpa only [iterateTensorObj_zero, Nat.add_zero, eqToHom_refl, Category.comp_id,
                  normalize_left_zero, whiskerLeft_id, Category.id_comp] using ih
              change (l (I p A) B).hom ▷ D ≫ ((P A B p 0).hom ▷ L) ▷ D ≫
                  (l (I p (A ⊗ B)) D).hom ≫ (P (A ⊗ B) D p 0).hom ▷ L ≫
                  (iterate T p).map (α_ A B D).hom ▷ L =
                (α_ (I p A ⊗ L) B D).hom ≫ (I p A ⊗ L) ◁ 𝟙 (B ⊗ D) ≫
                  (l (I p A) (B ⊗ D)).hom ≫ (P A (B ⊗ D) p 0).hom ▷ L
              simp only [whiskerLeft_id, Category.id_comp]
              let f : I p A ⊗ B ⟶ I p (A ⊗ B) := (P A B p 0).hom
              let g : I p (A ⊗ B) ⊗ D ⟶ I p ((A ⊗ B) ⊗ D) := (P (A ⊗ B) D p 0).hom
              change (l (I p A) B).hom ▷ D ≫ f ▷ L ▷ D ≫
                (l (I p (A ⊗ B)) D).hom ≫ g ▷ L ≫ (iterate T p).map (α_ A B D).hom ▷ L = _
              rw [moveTensorLeft_natural_first_assoc L f D, ← comp_whiskerRight,
                ← comp_whiskerRight,
                show f ▷ D ≫ g ≫ (iterate T p).map (α_ A B D).hom = _ from ih',
                comp_whiskerRight, assoc_left_step_assoc]
      | succ q ih =>
          have ih' : (P A B p q).hom ▷ D ≫ (P (A ⊗ B) D (p + q) 0).hom ≫
                (iterate T (p + q)).map (α_ A B D).hom =
              (α_ (I p A) (I q B) D).hom ≫ (I p A ◁ (P B D q 0).hom) ≫
                (P A (B ⊗ D) p q).hom := by
            simpa only [iterateTensorObj_zero, Nat.add_zero, eqToHom_refl, Category.comp_id]
              using ih
          change (P A B p (q + 1)).hom ▷ I 0 D ≫
            (P (A ⊗ B) D ((p + q) + 1) 0).hom ≫ _ = _
          simp only [left_succ L hL (A ⊗ B) D (p + q) 0,
            left_succ L hL B D q 0, right_succ, eqToHom_refl, Category.comp_id,
            comp_whiskerRight, whiskerLeft_comp, Category.assoc]
          change (r (I p A) (I q B)).hom ▷ D ≫ ((P A B p q).hom ▷ L) ▷ D ≫
              (l (I (p + q) (A ⊗ B)) D).hom ≫ (P (A ⊗ B) D (p + q) 0).hom ▷ L ≫
              (iterate T (p + q)).map (α_ A B D).hom ▷ L =
            (α_ (I p A) (I q B ⊗ L) D).hom ≫ (I p A ◁ (l (I q B) D).hom) ≫
              (I p A ◁ (P B D q 0).hom ▷ L) ≫
              (r (I p A) (I q (B ⊗ D))).hom ≫ (P A (B ⊗ D) p q).hom ▷ L
          rw [moveTensorLeft_natural_first_assoc L (P A B p q).hom D,
            ← comp_whiskerRight, ← comp_whiskerRight, ih', comp_whiskerRight, comp_whiskerRight,
            assoc_middle_step_assoc]
          simp only [moveTensorRight, Iso.symm_hom]
          let f : I q B ⊗ D ⟶ I q (B ⊗ D) := (P B D q 0).hom
          change _ ≫ _ ≫ (α_ (I p A) (I q B ⊗ D) L).inv ≫ (I p A ◁ f) ▷ L ≫ _ =
            _ ≫ _ ≫ (I p A ◁ (f ▷ L)) ≫ (α_ (I p A) (I q (B ⊗ D)) L).inv ≫ _
          rw [associator_inv_naturality_middle_assoc]
  | succ r₀ ih =>
      have h := congrArg (fun k => I k (A ⊗ B ⊗ D)) (Nat.add_assoc p q r₀)
      have he : ι (congrArg (fun k => I k (A ⊗ B ⊗ D)) (Nat.add_assoc p q (r₀ + 1))) =
          ι h ▷ L := by
        rw [eqToHom_whiskerRight]
      simp only [right_succ, whiskerLeft_comp, Category.assoc]
      rw [he]
      change (P A B p q).hom ▷ (I r₀ D ⊗ L) ≫
          (r (I (p + q) (A ⊗ B)) (I r₀ D)).hom ≫
          (P (A ⊗ B) D (p + q) r₀).hom ▷ L ≫
          (iterate T ((p + q) + r₀)).map (α_ A B D).hom ▷ L ≫ ι h ▷ L =
        (α_ (I p A) (I q B) (I r₀ D ⊗ L)).hom ≫
          (I p A ◁ (r (I q B) (I r₀ D)).hom) ≫
          (I p A ◁ (P B D q r₀).hom ▷ L) ≫
          (r (I p A) (I (q + r₀) (B ⊗ D))).hom ≫ (P A (B ⊗ D) p (q + r₀)).hom ▷ L
      rw [show (r (I (p + q) (A ⊗ B)) (I r₀ D)).hom =
          (α_ (I (p + q) (A ⊗ B)) (I r₀ D) L).inv from rfl,
        associator_inv_naturality_left_assoc, ← comp_whiskerRight, ← comp_whiskerRight,
        ← comp_whiskerRight]
      rw [show (P A B p q).hom ▷ I r₀ D ≫ (P (A ⊗ B) D (p + q) r₀).hom ≫
          (iterate T ((p + q) + r₀)).map (α_ A B D).hom ≫ ι h = _ from ih]
      rw [comp_whiskerRight, comp_whiskerRight]
      change (r (I p A ⊗ I q B) (I r₀ D)).hom ≫ _ = _
      rw [assoc_right_step_assoc]
      simp only [moveTensorRight, Iso.symm_hom, associator_inv_naturality_middle_assoc]

end

end CategoryTheory.Stabilization
