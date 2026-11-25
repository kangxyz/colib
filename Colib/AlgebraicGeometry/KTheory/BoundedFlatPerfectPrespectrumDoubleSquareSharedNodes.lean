/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareCommonSimplex

/-! Exact shared nodes required before the three native scalar surfaces can be pasted. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS
universe u
namespace CategoryTheory.Waldhausen.IteratedS.ModelSimplex

open SmallWaldhausenCategory

private theorem transportedReferenceNode_congr {V W : WideSubcategory preservesZero.{u}}
    {I : Type*} (F₀ : V ⟶ W) (S T : I → (V ⟶ W))
    (ρ : ∀ i, (S i).hom.toFunctor ≅ (T i).hom.toFunctor) {i j : I} (h : i = j)
    (ei : F₀.hom.toFunctor = (S i).hom.toFunctor)
    (ej : F₀.hom.toFunctor = (S j).hom.toFunctor) :
    (⟨T i, eqToIso ei ≪≫ ρ i⟩ : Σ F : V ⟶ W, F₀.hom.toFunctor ≅ F.hom.toFunctor) =
      ⟨T j, eqToIso ej ≪≫ ρ j⟩ := by
  subst j
  rfl

end CategoryTheory.Waldhausen.IteratedS.ModelSimplex

private theorem doubleSquareWhiskering_eqToHom {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    (L : A ⥤ B) (R : C ⥤ D) {F G : B ⥤ C} (e : F = G) :
    whiskerLeft L (whiskerRight (eqToHom e) R) =
      eqToHom (congrArg (fun K ↦ L ⋙ K ⋙ R) e) := by
  subst G
  ext x
  simp

private theorem doubleSquareWhiskering_eqToIso_trans {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    (L : A ⥤ B) (R : C ⥤ D) {F G H : B ⥤ C} (e : F = G) (ρ : G ≅ H) :
    isoWhiskerLeft L (isoWhiskerRight (eqToIso e ≪≫ ρ) R) =
      eqToIso (congrArg (fun K ↦ L ⋙ K ⋙ R) e) ≪≫ isoWhiskerLeft L (isoWhiskerRight ρ R) := by
  subst G
  simp

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareCommonSimplex
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

private theorem rightSourceEq {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (BoundedFlatPerfectTripleSimplex.source f g h).hom.toFunctor =
      (BoundedFlatPerfectBinarySimplex.sourceMap (f ≫ g) h).hom.toFunctor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedAboveFlatPerfectNormalizedPullback (Category.assoc f g h).symm)

private theorem rightRawReference {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    BoundedFlatPerfectSplitTripleSimplex.rightFirstGeometric f g h =
      eqToIso (rightSourceEq f g h) ≪≫ BoundedFlatPerfectBinarySimplex.first (f ≫ g) h := by
  unfold BoundedFlatPerfectSplitTripleSimplex.rightFirstGeometric
    BoundedFlatPerfectBinarySimplex.first
  exact doubleSquareWhiskering_eqToIso_trans AsSmall.down AsSmall.up _ _

private theorem rightNormalizedReference {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    BoundedFlatPerfectTripleSimplex.rightFirst f g h =
      eqToIso (rightSourceEq f g h) ≪≫ BoundedFlatPerfectBinarySimplex.total (f ≫ g) h := by
  unfold BoundedFlatPerfectTripleSimplex.rightFirst BoundedFlatPerfectBinarySimplex.total
  exact doubleSquareWhiskering_eqToIso_trans AsSmall.down AsSmall.up _ _

include hq in
private theorem middleFunctorEq : (BoundedFlatPerfectTripleSimplex.source c q p).hom.toFunctor =
    (BoundedFlatPerfectTripleSimplex.source q' b p).hom.toFunctor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedAboveFlatPerfectNormalizedPullback (middle_eq p q q' b c hq).symm)

include hp hq in
private theorem lastFunctorEq : (BoundedFlatPerfectTripleSimplex.source c q p).hom.toFunctor =
    (BoundedFlatPerfectTripleSimplex.source q' p' a).hom.toFunctor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedAboveFlatPerfectNormalizedPullback
      ((total_eq p q p' q' a b c hp hq).symm.trans
        (Category.assoc q' p' a)))

private theorem middleSourceIso_hom : (middleSourceIso p q q' b c hq).hom =
    eqToHom (middleFunctorEq p q q' b c hq) := by
  simp only [middleSourceIso, isoWhiskerLeft_hom, isoWhiskerRight_hom, eqToIso.hom,
    doubleSquareWhiskering_eqToHom]

private theorem lastSourceIso_hom : (lastSourceIso p q p' q' a b c hp hq).hom =
    eqToHom (lastFunctorEq p q p' q' a b c hp hq) := by
  simp only [lastSourceIso, isoWhiskerLeft_hom, isoWhiskerRight_hom, eqToIso.hom,
    doubleSquareWhiskering_eqToHom]

private theorem middleSourceIso_eq : middleSourceIso p q q' b c hq =
    eqToIso (middleFunctorEq p q q' b c hq) := Iso.ext (middleSourceIso_hom p q q' b c hq)

private theorem lastSourceIso_eq : lastSourceIso p q p' q' a b c hp hq =
    eqToIso (lastFunctorEq p q p' q' a b c hp hq) :=
  Iso.ext (lastSourceIso_hom p q p' q' a b c hp hq)

include hp hq in
/-- The original source transports identify the chosen binary source of the last chart. -/
theorem lastRightFunctorEq : (BoundedFlatPerfectTripleSimplex.source c q p).hom.toFunctor =
    (BoundedFlatPerfectBinarySimplex.sourceMap (q' ≫ p') a).hom.toFunctor :=
  (lastFunctorEq p q p' q' a b c hp hq).trans (rightSourceEq q' p' a)

/-- The last raw reference retains the original geometric binary comparison. -/
theorem lastRightRawReference :
    lastSourceIso p q p' q' a b c hp hq ≪≫
        BoundedFlatPerfectSplitTripleSimplex.rightFirstGeometric q' p' a =
      eqToIso (lastRightFunctorEq p q p' q' a b c hp hq) ≪≫
        BoundedFlatPerfectBinarySimplex.first (q' ≫ p') a := by
  rw [lastSourceIso_eq, rightRawReference, ← Iso.trans_assoc, eqToIso_trans]

/-- The last normalized reference retains the original total binary comparison. -/
theorem lastRightNormalizedReference :
    lastSourceIso p q p' q' a b c hp hq ≪≫ BoundedFlatPerfectTripleSimplex.rightFirst q' p' a =
      eqToIso (lastRightFunctorEq p q p' q' a b c hp hq) ≪≫
        BoundedFlatPerfectBinarySimplex.total (q' ≫ p') a := by
  rw [lastSourceIso_eq, rightNormalizedReference, ← Iso.trans_assoc, eqToIso_trans]

/-- The first actual square identifies the two complete source reference nodes. -/
theorem source_middle_shared : nodes p q p' q' a b c hp hq 0 =
    nodes p q p' q' a b c hp hq 8 := by
  change nodes p q p' q' a b c hp hq (Fin.castAdd 16 (0 : Fin 8)) =
    nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.castAdd 8 (0 : Fin 8)))
  rw [first_nodes, middle_nodes]
  apply ModelSimplex.reference_node_eq (middleFunctorEq p q q' b c hq)
  simpa only [BoundedFlatPerfectSplitTripleSimplex.references, Fin.cases_zero, Iso.refl_hom,
    Iso.trans_hom,
    Category.id_comp, Category.comp_id] using (middleSourceIso_hom p q q' b c hq).symm

/-- Both actual square equations identify the last complete source reference node. -/
theorem source_last_shared : nodes p q p' q' a b c hp hq 0 =
    nodes p q p' q' a b c hp hq 16 := by
  change nodes p q p' q' a b c hp hq (Fin.castAdd 16 (0 : Fin 8)) =
    nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.natAdd 8 (0 : Fin 8)))
  rw [first_nodes, last_nodes]
  apply ModelSimplex.reference_node_eq (lastFunctorEq p q p' q' a b c hp hq)
  simpa only [BoundedFlatPerfectSplitTripleSimplex.references, Fin.cases_zero, Iso.refl_hom,
    Iso.trans_hom,
    Category.id_comp, Category.comp_id] using (lastSourceIso_hom p q p' q' a b c hp hq).symm

/-- The second square identifies the actual shared raw binary-normalization intermediate. -/
theorem left_raw_shared : nodes p q p' q' a b c hp hq 9 =
    nodes p q p' q' a b c hp hq 17 := by
  change nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.castAdd 8 (1 : Fin 8))) =
    nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.natAdd 8 (1 : Fin 8)))
  rw [middle_nodes, last_nodes]
  change (⟨BoundedFlatPerfectBinarySimplex.intermediateMap q' (b ≫ p),
      middleSourceIso p q q' b c hq ≪≫ BoundedFlatPerfectBinarySimplex.first q' (b ≫ p)⟩ :
        Node p q c) =
    ⟨BoundedFlatPerfectBinarySimplex.intermediateMap q' (p' ≫ a),
      lastSourceIso p q p' q' a b c hp hq ≪≫ BoundedFlatPerfectBinarySimplex.first q' (p' ≫ a)⟩
  rw [middleSourceIso_eq, lastSourceIso_eq]
  exact ModelSimplex.transportedReferenceNode_congr (BoundedFlatPerfectTripleSimplex.source c q p)
    (fun k : B' ⟶ A ↦ BoundedFlatPerfectBinarySimplex.sourceMap q' k)
    (fun k ↦ BoundedFlatPerfectBinarySimplex.intermediateMap q' k)
    (fun k ↦ BoundedFlatPerfectBinarySimplex.first q' k) hp
    (middleFunctorEq p q q' b c hq) (lastFunctorEq p q p' q' a b c hp hq)

/-- The second square also identifies the actual normalized endpoint and its entire reference. -/
theorem left_normalized_shared : nodes p q p' q' a b c hp hq 10 =
    nodes p q p' q' a b c hp hq 18 := by
  change nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.castAdd 8 (2 : Fin 8))) =
    nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.natAdd 8 (2 : Fin 8)))
  rw [middle_nodes, last_nodes]
  change (⟨BoundedFlatPerfectBinarySimplex.targetMap q' (b ≫ p),
      middleSourceIso p q q' b c hq ≪≫ BoundedFlatPerfectBinarySimplex.total q' (b ≫ p)⟩ :
        Node p q c) =
    ⟨BoundedFlatPerfectBinarySimplex.targetMap q' (p' ≫ a),
      lastSourceIso p q p' q' a b c hp hq ≪≫ BoundedFlatPerfectBinarySimplex.total q' (p' ≫ a)⟩
  rw [middleSourceIso_eq, lastSourceIso_eq]
  exact ModelSimplex.transportedReferenceNode_congr (BoundedFlatPerfectTripleSimplex.source c q p)
    (fun k : B' ⟶ A ↦ BoundedFlatPerfectBinarySimplex.sourceMap q' k)
    (fun k ↦ BoundedFlatPerfectBinarySimplex.targetMap q' k)
    (fun k ↦ BoundedFlatPerfectBinarySimplex.total q' k) hp
    (middleFunctorEq p q q' b c hq) (lastFunctorEq p q p' q' a b c hp hq)

/-- The first square identifies the shared raw right intermediate and its entire reference. -/
theorem right_raw_shared : nodes p q p' q' a b c hp hq 4 =
    nodes p q p' q' a b c hp hq 12 := by
  change nodes p q p' q' a b c hp hq (Fin.castAdd 16 (4 : Fin 8)) =
    nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.castAdd 8 (4 : Fin 8)))
  rw [first_nodes, middle_nodes]
  change (⟨BoundedFlatPerfectBinarySimplex.intermediateMap (c ≫ q) p,
      BoundedFlatPerfectSplitTripleSimplex.rightFirstGeometric c q p⟩ : Node p q c) =
    ⟨BoundedFlatPerfectBinarySimplex.intermediateMap (q' ≫ b) p,
      middleSourceIso p q q' b c hq ≪≫
        BoundedFlatPerfectSplitTripleSimplex.rightFirstGeometric q' b p⟩
  rw [rightRawReference, rightRawReference, middleSourceIso_eq,
    ← Iso.trans_assoc, eqToIso_trans]
  exact ModelSimplex.transportedReferenceNode_congr (BoundedFlatPerfectTripleSimplex.source c q p)
    (fun k : C' ⟶ B ↦ BoundedFlatPerfectBinarySimplex.sourceMap k p)
    (fun k ↦ BoundedFlatPerfectBinarySimplex.intermediateMap k p)
    (fun k ↦ BoundedFlatPerfectBinarySimplex.first k p) hq
    (rightSourceEq c q p) ((middleFunctorEq p q q' b c hq).trans (rightSourceEq q' b p))

/-- The first square also identifies the shared normalized right endpoint and its reference. -/
theorem right_normalized_shared : nodes p q p' q' a b c hp hq 5 =
    nodes p q p' q' a b c hp hq 13 := by
  change nodes p q p' q' a b c hp hq (Fin.castAdd 16 (5 : Fin 8)) =
    nodes p q p' q' a b c hp hq (Fin.natAdd 8 (Fin.castAdd 8 (5 : Fin 8)))
  rw [first_nodes, middle_nodes]
  change (⟨BoundedFlatPerfectBinarySimplex.targetMap (c ≫ q) p,
      BoundedFlatPerfectTripleSimplex.rightFirst c q p⟩ : Node p q c) =
    ⟨BoundedFlatPerfectBinarySimplex.targetMap (q' ≫ b) p,
      middleSourceIso p q q' b c hq ≪≫ BoundedFlatPerfectTripleSimplex.rightFirst q' b p⟩
  rw [rightNormalizedReference, rightNormalizedReference, middleSourceIso_eq,
    ← Iso.trans_assoc, eqToIso_trans]
  exact ModelSimplex.transportedReferenceNode_congr (BoundedFlatPerfectTripleSimplex.source c q p)
    (fun k : C' ⟶ B ↦ BoundedFlatPerfectBinarySimplex.sourceMap k p)
    (fun k ↦ BoundedFlatPerfectBinarySimplex.targetMap k p)
    (fun k ↦ BoundedFlatPerfectBinarySimplex.total k p) hq
    (rightSourceEq c q p) ((middleFunctorEq p q q' b c hq).trans (rightSourceEq q' b p))

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareCommonSimplex
