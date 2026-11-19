/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.Basic

/-!
# Restriction of the coniveau tower to opens

Inverse images of the original supports induce restriction on each stage and window.
The exact sequences commute with restriction by the naturality of the nested-pair maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

private def restrictionCocone {I J C : Type*} [Category* I] [Category* J] [Category* C]
    (P : I ⥤ J) (F : I ⥤ C) (G : J ⥤ C) [HasColimit G] (η : F ⟶ P ⋙ G) : Cocone F :=
  (Cocone.precompose η).obj ((colimit.cocone G).whisker P)

private theorem restrictionCocone_desc_ι {I J C : Type*}
    [Category* I] [Category* J] [Category* C]
    (P : I ⥤ J) (F : I ⥤ C) (G : J ⥤ C) [HasColimit F] [HasColimit G]
    (η : F ⟶ P ⋙ G) (i : I) :
    colimit.ι F i ≫ colimit.desc F (restrictionCocone P F G η) =
      η.app i ≫ colimit.ι G (P.obj i) :=
  colimit.ι_desc (restrictionCocone P F G η) i

private def reassociateStageFunctor {I J C D A : Type*}
    [Category* I] [Category* J] [Category* C] [Category* D] [Category* A]
    (F : I ⥤ J) (G : J ⥤ C) (P : C ⥤ D) (H : D ⥤ A) :
    F ⋙ G ⋙ P ⋙ H ≅ (F ⋙ G ⋙ P) ⋙ H :=
  Functor.isoWhiskerLeft F (Functor.associator G P H).symm ≪≫
    (Functor.associator F (G ⋙ P) H).symm

private def transportWhiskeredRestriction {I J D A : Type*}
    [Category* I] [Category* J] [Category* D] [Category* A]
    (P : I ⥤ J) (H : D ⥤ A) {F : I ⥤ A} {G : J ⥤ A} {L : I ⥤ D} {M : J ⥤ D}
    (eF : F ≅ L ⋙ H) (eG : G ≅ M ⋙ H) (r : L ⟶ P ⋙ M) : F ⟶ P ⋙ G :=
  eF.hom ≫ Functor.whiskerRight r H ≫ (Functor.associator P M H).hom ≫
    Functor.whiskerLeft P eG.inv

private theorem transportWhiskeredRestriction_app {I J D A : Type*}
    [Category* I] [Category* J] [Category* D] [Category* A]
    (P : I ⥤ J) (H : D ⥤ A) {F : I ⥤ A} {G : J ⥤ A} {L : I ⥤ D} {M : J ⥤ D}
    (eF : F ≅ L ⋙ H) (eG : G ≅ M ⋙ H) (r : L ⟶ P ⋙ M) (i : I) :
    (transportWhiskeredRestriction P H eF eG r).app i =
      eF.hom.app i ≫ H.map (r.app i) ≫ eG.inv.app (P.obj i) := by
  simp [transportWhiskeredRestriction]

private theorem restrict_comp_identities {C : Type*} [Category* C] {A B : C}
    (i : A ⟶ A) (m : A ⟶ B) (j : B ⟶ B) (hi : i = 𝟙 A) (hj : j = 𝟙 B) :
    i ≫ m ≫ j = m :=
  (congrArg₂ (fun p q ↦ p ≫ m ≫ q) hi hj).trans
    ((Category.id_comp (m ≫ 𝟙 _)).trans (Category.comp_id m))

private theorem postcompose_comp_eq {C : Type*} [Category* C] {A B D E Q : C}
    {a : A ⟶ B} {b : B ⟶ E} {c : A ⟶ D} {d : D ⟶ E}
    (h : a ≫ b = c ≫ d) (m : E ⟶ Q) : a ≫ b ≫ m = c ≫ d ≫ m :=
  (Category.assoc a b m).symm.trans ((congrArg (· ≫ m) h).trans (Category.assoc c d m))

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

variable {X Y T : Sm(k)}

private def supportStageArrows (X : Sm(k)) (a : ℕ) :
    ConiveauSupports k X a ⥤ (Arrow Sm(k))ᵒᵖ :=
  Monotone.functor (f := fun Z : ConiveauSupports k X a ↦ Z.1) (fun _ _ h ↦ h) ⋙
    opOp (TopologicalSpace.Closeds X.left) ⋙ (supportOpenPairFunctor k X).op

private def supportWindowArrows (X : Sm(k)) (a b : ℕ) :
    ConiveauSupportPairs k X a b ⥤ (Arrow Sm(k))ᵒᵖ :=
  opOp (ConiveauSupportPairs k X a b) ⋙ (coniveauSupportPairsInclusion k X a b).op

private def supportStageArrowsRestrict (a : ℕ) (f : Y ⟶ X) [IsOpenImmersion f.left] :
    supportStageArrows k X a ⟶ coniveauSupportsPreimage k f a ⋙ supportStageArrows k Y a where
  app Z := (supportOpenPairPreimageMap k f Z.1).op
  naturality Z W m := by
    let m' : Z.1 ⟶ W.1 := homOfLE m.le
    exact congrArg Quiver.Hom.op (supportOpenPairPreimageMap_naturality k f m').symm

private def supportWindowArrowsRestrict (a b : ℕ) (f : Y ⟶ X) [IsOpenImmersion f.left] :
    supportWindowArrows k X a b ⟶
      coniveauSupportPairsPreimage k f a b ⋙ supportWindowArrows k Y a b where
  app ZW := (supportPairPreimageMap k f ZW).op
  naturality _ _ m :=
    congrArg Quiver.Hom.op (supportPairPreimageMap_naturality k f m).symm

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "DM(" field ")" => EffectiveMotivesMinus field

attribute [local irreducible] effectivePairCohomology

set_option maxHeartbeats 550000 in
-- The original stage diagram is a right-associated composite of four functors.
private def supportStageEvaluationIso (X : Sm(k)) (K : DM(k)) (n : ℤ) (a : ℕ) :
    coniveauCohomologyDiagram k X K n a ≅ supportStageArrows k X a ⋙
      effectivePairCohomology k K n := by
  let F := Monotone.functor (f := fun Z : ConiveauSupports k X a ↦ Z.1) (fun _ _ h ↦ h)
  let G := opOp (TopologicalSpace.Closeds X.left)
  let P := (supportOpenPairFunctor k X).op
  let H := effectivePairCohomology k K n
  exact reassociateStageFunctor F G P H

set_option maxHeartbeats 550000 in
-- The relative diagram is a right-associated composite of three functors.
private def supportWindowEvaluationIso (X : Sm(k)) (K : DM(k)) (n : ℤ) (a b : ℕ) :
    coniveauRelativeSupportDiagram k X K n a b ≅ supportWindowArrows k X a b ⋙
      effectivePairCohomology k K n :=
  (Functor.associator (opOp (ConiveauSupportPairs k X a b))
    (coniveauSupportPairsInclusion k X a b).op (effectivePairCohomology k K n)).symm

set_option maxHeartbeats 550000 in
-- Use the explicit associators to compare the original and the whiskered stage diagrams.
private def coniveauCohomologyDiagramRestrict (K : DM(k)) (n : ℤ) (a : ℕ)
    (f : Y ⟶ X) [IsOpenImmersion f.left] :
    coniveauCohomologyDiagram k X K n a ⟶
      coniveauSupportsPreimage k f a ⋙ coniveauCohomologyDiagram k Y K n a :=
  transportWhiskeredRestriction (coniveauSupportsPreimage k f a) (effectivePairCohomology k K n)
    (supportStageEvaluationIso k X K n a) (supportStageEvaluationIso k Y K n a)
    (supportStageArrowsRestrict k a f)

set_option maxHeartbeats 550000 in
-- The explicit associators compare the original and the whiskered relative-support diagrams.
private def coniveauRelativeSupportDiagramRestrict (K : DM(k)) (n : ℤ) (a b : ℕ)
    (f : Y ⟶ X) [IsOpenImmersion f.left] :
    coniveauRelativeSupportDiagram k X K n a b ⟶
      coniveauSupportPairsPreimage k f a b ⋙ coniveauRelativeSupportDiagram k Y K n a b :=
  transportWhiskeredRestriction (coniveauSupportPairsPreimage k f a b)
    (effectivePairCohomology k K n) (supportWindowEvaluationIso k X K n a b)
    (supportWindowEvaluationIso k Y K n a b) (supportWindowArrowsRestrict k a b f)

set_option maxHeartbeats 550000 in
-- The components of the associators identify the literal groups of the two diagrams.
private theorem coniveauCohomologyDiagramRestrict_app (K : DM(k)) (n : ℤ) {a : ℕ}
    (f : Y ⟶ X) [IsOpenImmersion f.left] (Z : ConiveauSupports k X a) :
    (coniveauCohomologyDiagramRestrict k K n a f).app Z =
      closedSupportCohomologyPreimageMap k X K n f Z.1 := by
  let P := coniveauSupportsPreimage k f a
  let H := effectivePairCohomology k K n
  let eX := supportStageEvaluationIso k X K n a
  let eY := supportStageEvaluationIso k Y K n a
  let r := supportStageArrowsRestrict k a f
  have h := transportWhiskeredRestriction_app P H eX eY r Z
  let m := H.map (supportOpenPairPreimageMap k f Z.1).op
  have hX : eX.hom.app Z = 𝟙 _ := by
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.comp_id _
  have hY : eY.inv.app (P.obj Z) = 𝟙 _ := by
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.comp_id _
  exact h.trans (restrict_comp_identities (eX.hom.app Z) m (eY.inv.app (P.obj Z)) hX hY)

set_option maxHeartbeats 550000 in
-- The associators have identity components at the original nested pair.
private theorem coniveauRelativeSupportDiagramRestrict_app (K : DM(k)) (n : ℤ) {a b : ℕ}
    (f : Y ⟶ X) [IsOpenImmersion f.left] (ZW : ConiveauSupportPairs k X a b) :
    (coniveauRelativeSupportDiagramRestrict k K n a b f).app ZW =
      relativeSupportCohomologyPreimageMap k X K n f ZW := by
  let P := coniveauSupportPairsPreimage k f a b
  let H := effectivePairCohomology k K n
  let eX := supportWindowEvaluationIso k X K n a b
  let eY := supportWindowEvaluationIso k Y K n a b
  let r := supportWindowArrowsRestrict k a b f
  have h := transportWhiskeredRestriction_app P H eX eY r ZW
  let m := H.map (supportPairPreimageMap k f ZW).op
  have hX : eX.hom.app ZW = 𝟙 _ := rfl
  have hY : eY.inv.app (P.obj ZW) = 𝟙 _ := rfl
  exact h.trans (restrict_comp_identities (eX.hom.app ZW) m (eY.inv.app (P.obj ZW)) hX hY)

variable [UnivLE.{u, w'}]

set_option maxHeartbeats 800000 in
-- The shared support diagram has colimits over two ambient schemes.
/-- Restriction of a coniveau stage along an open immersion. -/
@[no_expose]
def coniveauCohomologyRestrict (K : DM(k)) (n : ℤ) (a : ℕ)
    (f : Y ⟶ X) [IsOpenImmersion f.left] :
    coniveauCohomology k X K n a ⟶ coniveauCohomology k Y K n a :=
  let P := coniveauSupportsPreimage k f a
  let F := coniveauCohomologyDiagram k X K n a
  let G := coniveauCohomologyDiagram k Y K n a
  colimit.desc F (restrictionCocone P F G (coniveauCohomologyDiagramRestrict k K n a f))

/-- Restriction of a coniveau window along an open immersion. -/
@[no_expose]
def coniveauRelativeSupportRestrict (K : DM(k)) (n : ℤ) (a b : ℕ)
    (f : Y ⟶ X) [IsOpenImmersion f.left] :
    coniveauRelativeSupportCohomology k X K n a b ⟶
      coniveauRelativeSupportCohomology k Y K n a b :=
  let P := coniveauSupportPairsPreimage k f a b
  let F := coniveauRelativeSupportDiagram k X K n a b
  let G := coniveauRelativeSupportDiagram k Y K n a b
  colimit.desc F (restrictionCocone P F G (coniveauRelativeSupportDiagramRestrict k K n a b f))

set_option maxHeartbeats 850000 in
-- The generator formula compares a restricted and an original cohomology diagram.
/-- Stage restriction on a representative is precomposition with the original map of pairs. -/
theorem ι_coniveauCohomologyRestrict (K : DM(k)) (n : ℤ) {a : ℕ}
    (f : Y ⟶ X) [IsOpenImmersion f.left] (Z : ConiveauSupports k X a) :
    colimit.ι (coniveauCohomologyDiagram k X K n a) Z ≫ coniveauCohomologyRestrict k K n a f =
      closedSupportCohomologyPreimageMap k X K n f Z.1 ≫
        colimit.ι (coniveauCohomologyDiagram k Y K n a)
          ((coniveauSupportsPreimage k f a).obj Z) := by
  let P := coniveauSupportsPreimage k f a
  let F := coniveauCohomologyDiagram k X K n a
  let G := coniveauCohomologyDiagram k Y K n a
  have h := restrictionCocone_desc_ι P F G (coniveauCohomologyDiagramRestrict k K n a f) Z
  exact h.trans (congrArg (· ≫ colimit.ι G (P.obj Z))
    (coniveauCohomologyDiagramRestrict_app k K n f Z))

set_option maxHeartbeats 550000 in
-- The represented source group is identified with its diagram evaluation.
/-- The stage generator formula followed by a map out of the restricted stage. -/
theorem ι_coniveauCohomologyRestrict_assoc (K : DM(k)) (n : ℤ) {a : ℕ}
    (f : Y ⟶ X) [IsOpenImmersion f.left] (Z : ConiveauSupports k X a)
    {A : AddCommGrpCat.{w'}} (m : coniveauCohomology k Y K n a ⟶ A) :
    colimit.ι (coniveauCohomologyDiagram k X K n a) Z ≫ coniveauCohomologyRestrict k K n a f ≫ m =
      closedSupportCohomologyPreimageMap k X K n f Z.1 ≫
        colimit.ι (coniveauCohomologyDiagram k Y K n a)
          ((coniveauSupportsPreimage k f a).obj Z) ≫ m :=
  postcompose_comp_eq (ι_coniveauCohomologyRestrict k K n f Z) m

set_option maxHeartbeats 850000 in
-- The generator formula compares a restricted and an original cohomology diagram.
/-- Window restriction on a representative is the original relative restriction. -/
theorem ι_coniveauRelativeSupportRestrict (K : DM(k)) (n : ℤ) {a b : ℕ}
    (f : Y ⟶ X) [IsOpenImmersion f.left] (ZW : ConiveauSupportPairs k X a b) :
    colimit.ι (coniveauRelativeSupportDiagram k X K n a b) ZW ≫
        coniveauRelativeSupportRestrict k K n a b f =
      relativeSupportCohomologyPreimageMap k X K n f ZW ≫
        colimit.ι (coniveauRelativeSupportDiagram k Y K n a b)
          ((coniveauSupportPairsPreimage k f a b).obj ZW) := by
  let P := coniveauSupportPairsPreimage k f a b
  let F := coniveauRelativeSupportDiagram k X K n a b
  let G := coniveauRelativeSupportDiagram k Y K n a b
  have h := restrictionCocone_desc_ι P F G (coniveauRelativeSupportDiagramRestrict k K n a b f) ZW
  exact h.trans (congrArg (· ≫ colimit.ι G (P.obj ZW))
    (coniveauRelativeSupportDiagramRestrict_app k K n f ZW))

set_option maxHeartbeats 550000 in
-- The three object groups are the corresponding evaluations of the two pair diagrams.
/-- The window generator formula followed by a map out of the restricted window. -/
theorem ι_coniveauRelativeSupportRestrict_assoc (K : DM(k)) (n : ℤ) {a b : ℕ}
    (f : Y ⟶ X) [IsOpenImmersion f.left] (ZW : ConiveauSupportPairs k X a b)
    {A : AddCommGrpCat.{w'}} (m : coniveauRelativeSupportCohomology k Y K n a b ⟶ A) :
    colimit.ι (coniveauRelativeSupportDiagram k X K n a b) ZW ≫
        coniveauRelativeSupportRestrict k K n a b f ≫ m =
      relativeSupportCohomologyPreimageMap k X K n f ZW ≫
        colimit.ι (coniveauRelativeSupportDiagram k Y K n a b)
          ((coniveauSupportPairsPreimage k f a b).obj ZW) ≫ m :=
  postcompose_comp_eq (ι_coniveauRelativeSupportRestrict k K n f ZW) m

set_option maxHeartbeats 850000 in
-- Functoriality compares the same cohomology classes in two colimit diagrams.
/-- The identity restricts a coniveau stage by the identity. -/
theorem coniveauCohomologyRestrict_id (K : DM(k)) (n : ℤ) (a : ℕ) (X : Sm(k)) :
    coniveauCohomologyRestrict k K n a (𝟙 X) = 𝟙 _ := by
  apply colimit.hom_ext
  intro Z
  rw [ι_coniveauCohomologyRestrict, Category.comp_id]
  let H := effectivePairCohomology k K n
  let A := op (Arrow.mk (supportOpenInclusion k X Z.1))
  have h : (supportOpenPairPreimageMap k (𝟙 X) Z.1).op = 𝟙 A :=
    congrArg Quiver.Hom.op (supportOpenPairPreimageMap_id k Z.1)
  change H.map (supportOpenPairPreimageMap k (𝟙 X) Z.1).op ≫
      colimit.ι (coniveauCohomologyDiagram k X K n a) Z =
    colimit.ι (coniveauCohomologyDiagram k X K n a) Z
  exact ((H.congr_map h).trans (H.map_id A)) ▸ Category.id_comp _

set_option maxHeartbeats 850000 in
-- Functoriality compares the same cohomology classes in two colimit diagrams.
/-- Restriction of coniveau stages is contravariantly functorial. -/
theorem coniveauCohomologyRestrict_comp (K : DM(k)) (n : ℤ) (a : ℕ)
    (f : T ⟶ Y) (g : Y ⟶ X) [IsOpenImmersion f.left] [IsOpenImmersion g.left] :
    coniveauCohomologyRestrict k K n a (f ≫ g) =
      coniveauCohomologyRestrict k K n a g ≫ coniveauCohomologyRestrict k K n a f := by
  apply colimit.hom_ext
  intro Z
  rw [ι_coniveauCohomologyRestrict, ι_coniveauCohomologyRestrict_assoc]
  let H := effectivePairCohomology k K n
  let r := supportOpenPairPreimageMap k (f ≫ g) Z.1
  let r₁ := supportOpenPairPreimageMap k f (supportPreimage k g Z.1)
  let r₂ := supportOpenPairPreimageMap k g Z.1
  let t := colimit.ι (coniveauCohomologyDiagram k T K n a)
    ((coniveauSupportsPreimage k (f ≫ g) a).obj Z)
  have h : H.map r.op = H.map r₂.op ≫ H.map r₁.op :=
    (H.congr_map (congrArg Quiver.Hom.op (supportOpenPairPreimageMap_comp k f g Z.1))).trans
      (H.map_comp r₂.op r₁.op)
  have ht : H.map r.op ≫ t = H.map r₂.op ≫ H.map r₁.op ≫ t :=
    (congrArg (· ≫ t) h).trans (Category.assoc _ _ _)
  let Zg := (coniveauSupportsPreimage k g a).obj Z
  have hf := ι_coniveauCohomologyRestrict k K n f Zg
  exact ht.trans (congrArg (closedSupportCohomologyPreimageMap k X K n g Z.1 ≫ ·) hf).symm

set_option maxHeartbeats 850000 in
-- Functoriality compares the same cohomology classes in two colimit diagrams.
/-- The identity restricts a coniveau window by the identity. -/
theorem coniveauRelativeSupportRestrict_id (K : DM(k)) (n : ℤ) (a b : ℕ) (X : Sm(k)) :
    coniveauRelativeSupportRestrict k K n a b (𝟙 X) = 𝟙 _ := by
  apply colimit.hom_ext
  intro ZW
  rw [ι_coniveauRelativeSupportRestrict, Category.comp_id]
  let H := effectivePairCohomology k K n
  let A := op ((coniveauSupportPairsInclusion k X a b).obj (op ZW))
  have h : (supportPairPreimageMap k (𝟙 X) ZW).op = 𝟙 A :=
    congrArg Quiver.Hom.op (supportPairPreimageMap_id k ZW)
  change H.map (supportPairPreimageMap k (𝟙 X) ZW).op ≫
      colimit.ι (coniveauRelativeSupportDiagram k X K n a b) ZW =
    colimit.ι (coniveauRelativeSupportDiagram k X K n a b) ZW
  exact ((H.congr_map h).trans (H.map_id A)) ▸ Category.id_comp _

set_option maxHeartbeats 850000 in
-- Functoriality compares the same cohomology classes in two colimit diagrams.
/-- Restriction of coniveau windows is contravariantly functorial. -/
theorem coniveauRelativeSupportRestrict_comp (K : DM(k)) (n : ℤ) (a b : ℕ)
    (f : T ⟶ Y) (g : Y ⟶ X) [IsOpenImmersion f.left] [IsOpenImmersion g.left] :
    coniveauRelativeSupportRestrict k K n a b (f ≫ g) =
      coniveauRelativeSupportRestrict k K n a b g ≫
        coniveauRelativeSupportRestrict k K n a b f := by
  apply colimit.hom_ext
  intro ZW
  rw [ι_coniveauRelativeSupportRestrict, ι_coniveauRelativeSupportRestrict_assoc,
    ι_coniveauRelativeSupportRestrict]
  let H := effectivePairCohomology k K n
  let r := supportPairPreimageMap k (f ≫ g) ZW
  let r₁ := supportPairPreimageMap k f ((coniveauSupportPairsPreimage k g a b).obj ZW)
  let r₂ := supportPairPreimageMap k g ZW
  let t := colimit.ι (coniveauRelativeSupportDiagram k T K n a b)
    ((coniveauSupportPairsPreimage k (f ≫ g) a b).obj ZW)
  have h : H.map r.op = H.map r₂.op ≫ H.map r₁.op :=
    (H.congr_map (congrArg Quiver.Hom.op (supportPairPreimageMap_comp k f g ZW))).trans
      (H.map_comp r₂.op r₁.op)
  have ht : H.map r.op ≫ t = H.map r₂.op ≫ H.map r₁.op ≫ t :=
    (congrArg (· ≫ t) h).trans (Category.assoc _ _ _)
  exact ht

set_option maxHeartbeats 850000 in
-- Functoriality compares the same cohomology classes in two colimit diagrams.
/-- The support transitions commute with open restriction. -/
theorem coniveauCohomologyTransition_restrict_naturality (K : DM(k)) (n : ℤ)
    {a b : ℕ} (hab : a ≤ b) (f : Y ⟶ X) [IsOpenImmersion f.left] :
    coniveauCohomologyTransition k X K n hab ≫ coniveauCohomologyRestrict k K n a f =
      coniveauCohomologyRestrict k K n b f ≫ coniveauCohomologyTransition k Y K n hab := by
  apply colimit.hom_ext
  intro Z
  rw [ι_coniveauCohomologyTransition_assoc, ι_coniveauCohomologyRestrict,
    ι_coniveauCohomologyRestrict_assoc]
  let Z' := (coniveauSupportsPreimage k f b).obj Z
  have h := ι_coniveauCohomologyTransition k Y K n hab Z'
  exact (congrArg (closedSupportCohomologyPreimageMap k X K n f Z.1 ≫ ·) h).symm

set_option maxHeartbeats 850000 in
-- The final projection presents a stage generator by a pair of supports.
/-- The original map from a support stage to a window commutes with open restriction. -/
theorem coniveauCohomologyToWindow_restrict_naturality (K : DM(k)) (n : ℤ)
    (a b : ℕ) (f : Y ⟶ X) [IsOpenImmersion f.left] :
    coniveauCohomologyToWindow k X K n a b ≫ coniveauRelativeSupportRestrict k K n a b f =
      coniveauCohomologyRestrict k K n a f ≫ coniveauCohomologyToWindow k Y K n a b := by
  apply colimit.hom_ext
  intro W
  let ZW : ConiveauSupportPairs k X a b :=
    ⟨(⊥, W), (show (⊥ : TopologicalSpace.Closeds X.left) ≤ W.1 from bot_le)⟩
  let ZW' := (coniveauSupportPairsPreimage k f a b).obj ZW
  have h := postcompose_comp_eq (ι_coniveauCohomologyToWindow k X K n ZW)
    (coniveauRelativeSupportRestrict k K n a b f)
  rw [h, ι_coniveauRelativeSupportRestrict, ι_coniveauCohomologyRestrict_assoc]
  change (coniveauRelativeSupportRestriction k X K n a b).app ZW ≫
      relativeSupportCohomologyPreimageMap k X K n f ZW ≫
        colimit.ι (coniveauRelativeSupportDiagram k Y K n a b) ZW' =
    closedSupportCohomologyPreimageMap k X K n f ZW.1.2.1 ≫
      colimit.ι (coniveauCohomologyDiagram k Y K n a) ZW'.1.2 ≫
        coniveauCohomologyToWindow k Y K n a b
  have hNat := coniveauRelativeSupportRestriction_app_naturality_assoc k X K n f ZW
    (colimit.ι (coniveauRelativeSupportDiagram k Y K n a b) ZW')
  have hY := ι_coniveauCohomologyToWindow k Y K n ZW'
  exact hNat.trans (congrArg (closedSupportCohomologyPreimageMap k X K n f W.1 ≫ ·) hY).symm

set_option maxHeartbeats 850000 in
-- The calculation combines restriction generators in two consecutive degrees.
/-- The signed connecting map commutes with open restriction. -/
theorem coniveauWindowBoundary_restrict_naturality (K : DM(k)) (n : ℤ)
    {a b : ℕ} (hab : a ≤ b) (f : Y ⟶ X) [IsOpenImmersion f.left] :
    coniveauWindowBoundary k X K n hab ≫ coniveauCohomologyRestrict k K (n + 1) b f =
      coniveauRelativeSupportRestrict k K n a b f ≫ coniveauWindowBoundary k Y K n hab := by
  apply colimit.hom_ext
  intro ZW
  let ZW' := (coniveauSupportPairsPreimage k f a b).obj ZW
  let B := coniveauRelativeSupportBoundary k X K n a b
  let r := relativeSupportCohomologyPreimageMap k X K n f ZW
  have h₁ := postcompose_comp_eq (ι_coniveauWindowBoundary k X K n hab ZW)
    (coniveauCohomologyRestrict k K (n + 1) b f)
  have h₂ := congrArg (B.app ZW ≫ ·) (ι_coniveauCohomologyRestrict k K (n + 1) f ZW.1.1)
  have h₃ := postcompose_comp_eq (coniveauRelativeSupportBoundary_app_naturality k X K n f ZW)
    (colimit.ι (coniveauCohomologyDiagram k Y K (n + 1) b) ZW'.1.1)
  have h₄ := congrArg (r ≫ ·) (ι_coniveauWindowBoundary k Y K n hab ZW')
  have h₅ := ι_coniveauRelativeSupportRestrict_assoc k K n f ZW
    (coniveauWindowBoundary k Y K n hab)
  exact h₁.trans (h₂.trans (h₃.trans (h₄.symm.trans h₅.symm)))

private theorem coniveauCohomologyRestrict_congr (K : DM(k)) (n : ℤ) (a : ℕ)
    {f g : Y ⟶ X} [IsOpenImmersion f.left] [IsOpenImmersion g.left] (h : f = g) :
    coniveauCohomologyRestrict k K n a f = coniveauCohomologyRestrict k K n a g := by
  subst g
  rfl

/-- Equal ambient open immersions induce the same restriction of a window. -/
theorem coniveauRelativeSupportRestrict_congr (K : DM(k)) (n : ℤ) (a b : ℕ)
    {f g : Y ⟶ X} [IsOpenImmersion f.left] [IsOpenImmersion g.left] (h : f = g) :
    coniveauRelativeSupportRestrict k K n a b f = coniveauRelativeSupportRestrict k K n a b g := by
  subst g
  rfl

variable (X)

/-- An actual open of the ambient smooth scheme comes with its open immersion. -/
instance openInclusion_isOpenImmersion (U : X.left.Opens) :
    IsOpenImmersion (SmoothSite.openInclusion X U).left :=
  inferInstanceAs (IsOpenImmersion (AlgebraicGeometry.Scheme.Opens.ι U))

/-- An inclusion in the smooth-site opens functor is an open immersion of schemes. -/
instance opensFunctor_map_isOpenImmersion {U V : X.left.Opens} (f : U ⟶ V) :
    IsOpenImmersion ((SmoothSite.opensFunctor X).map f).left :=
  inferInstanceAs (IsOpenImmersion (X.left.homOfLE f.le))

/-- Restriction of a coniveau stage to an actual open of the ambient scheme. -/
@[no_expose]
def coniveauCohomologyOpenRestriction (K : DM(k)) (n : ℤ) (a : ℕ) (U : X.left.Opens) :
    coniveauCohomology k X K n a ⟶
      coniveauCohomology k ((SmoothSite.opensFunctor X).obj U) K n a :=
  coniveauCohomologyRestrict k K n a (SmoothSite.openInclusion X U)

/-- Restriction of a coniveau window to an actual open of the ambient scheme. -/
@[no_expose]
def coniveauRelativeSupportOpenRestriction (K : DM(k)) (n : ℤ) (a b : ℕ)
    (U : X.left.Opens) : coniveauRelativeSupportCohomology k X K n a b ⟶
      coniveauRelativeSupportCohomology k ((SmoothSite.opensFunctor X).obj U) K n a b :=
  coniveauRelativeSupportRestrict k K n a b (SmoothSite.openInclusion X U)

/-- The window restriction to an actual open uses its original ambient inclusion. -/
theorem coniveauRelativeSupportOpenRestriction_eq_restrict (K : DM(k)) (n : ℤ) (a b : ℕ)
    (U : X.left.Opens) : coniveauRelativeSupportOpenRestriction k X K n a b U =
      coniveauRelativeSupportRestrict k K n a b (SmoothSite.openInclusion X U) := by
  unfold coniveauRelativeSupportOpenRestriction
  rfl

/-- Restriction of support stages between actual opens of a fixed smooth scheme. -/
def coniveauCohomologyOpenMap (K : DM(k)) (n : ℤ) (a : ℕ) {U V : X.left.Opens} (f : U ⟶ V) :
    coniveauCohomology k ((SmoothSite.opensFunctor X).obj V) K n a ⟶
      coniveauCohomology k ((SmoothSite.opensFunctor X).obj U) K n a :=
  coniveauCohomologyRestrict k K n a ((SmoothSite.opensFunctor X).map f)

/-- Restriction of windows between actual opens of a fixed smooth scheme. -/
@[no_expose]
def coniveauRelativeSupportOpenMap (K : DM(k)) (n : ℤ) (a b : ℕ)
    {U V : X.left.Opens} (f : U ⟶ V) :
    coniveauRelativeSupportCohomology k ((SmoothSite.opensFunctor X).obj V) K n a b ⟶
      coniveauRelativeSupportCohomology k ((SmoothSite.opensFunctor X).obj U) K n a b :=
  coniveauRelativeSupportRestrict k K n a b ((SmoothSite.opensFunctor X).map f)

/-- Restriction between actual opens uses the corresponding ambient morphism. -/
theorem coniveauRelativeSupportOpenMap_eq_restrict (K : DM(k)) (n : ℤ) (a b : ℕ)
    {U V : X.left.Opens} (f : U ⟶ V) : coniveauRelativeSupportOpenMap k X K n a b f =
      coniveauRelativeSupportRestrict k K n a b ((SmoothSite.opensFunctor X).map f) := by
  unfold coniveauRelativeSupportOpenMap
  rfl

/-- Identity law for restriction of stages between actual opens. -/
theorem coniveauCohomologyOpenMap_id (K : DM(k)) (n : ℤ) (a : ℕ) (U : X.left.Opens) :
    coniveauCohomologyOpenMap k X K n a (𝟙 U) = 𝟙 _ :=
  (coniveauCohomologyRestrict_congr k K n a ((SmoothSite.opensFunctor X).map_id U)).trans
    (coniveauCohomologyRestrict_id k K n a _)

/-- Composition law for restriction of stages between actual opens. -/
theorem coniveauCohomologyOpenMap_comp (K : DM(k)) (n : ℤ) (a : ℕ) {U V W : X.left.Opens}
    (f : U ⟶ V) (g : V ⟶ W) :
    coniveauCohomologyOpenMap k X K n a (f ≫ g) =
      coniveauCohomologyOpenMap k X K n a g ≫ coniveauCohomologyOpenMap k X K n a f :=
  (coniveauCohomologyRestrict_congr k K n a ((SmoothSite.opensFunctor X).map_comp f g)).trans
    (coniveauCohomologyRestrict_comp k K n a _ _)

/-- Identity law for restriction of windows between actual opens. -/
theorem coniveauRelativeSupportOpenMap_id (K : DM(k)) (n : ℤ) (a b : ℕ) (U : X.left.Opens) :
    coniveauRelativeSupportOpenMap k X K n a b (𝟙 U) = 𝟙 _ :=
  (coniveauRelativeSupportRestrict_congr k K n a b ((SmoothSite.opensFunctor X).map_id U)).trans
    (coniveauRelativeSupportRestrict_id k K n a b _)

/-- Composition law for restriction of windows between actual opens. -/
theorem coniveauRelativeSupportOpenMap_comp (K : DM(k)) (n : ℤ) (a b : ℕ) {U V W : X.left.Opens}
    (f : U ⟶ V) (g : V ⟶ W) :
    coniveauRelativeSupportOpenMap k X K n a b (f ≫ g) =
      coniveauRelativeSupportOpenMap k X K n a b g ≫
        coniveauRelativeSupportOpenMap k X K n a b f :=
  (coniveauRelativeSupportRestrict_congr k K n a b ((SmoothSite.opensFunctor X).map_comp f g)).trans
    (coniveauRelativeSupportRestrict_comp k K n a b _ _)

/-- Naturality of the support transitions between actual opens. -/
theorem coniveauCohomologyTransition_openMap_naturality (K : DM(k)) (n : ℤ)
    {a b : ℕ} (hab : a ≤ b) {U V : X.left.Opens} (f : U ⟶ V) :
    coniveauCohomologyTransition k ((SmoothSite.opensFunctor X).obj V) K n hab ≫
        coniveauCohomologyOpenMap k X K n a f =
      coniveauCohomologyOpenMap k X K n b f ≫
        coniveauCohomologyTransition k ((SmoothSite.opensFunctor X).obj U) K n hab :=
  coniveauCohomologyTransition_restrict_naturality k K n hab ((SmoothSite.opensFunctor X).map f)

/-- Naturality of the stage-to-window maps between actual opens. -/
theorem coniveauCohomologyToWindow_openMap_naturality (K : DM(k)) (n : ℤ)
    (a b : ℕ) {U V : X.left.Opens} (f : U ⟶ V) :
    coniveauCohomologyToWindow k ((SmoothSite.opensFunctor X).obj V) K n a b ≫
        coniveauRelativeSupportOpenMap k X K n a b f =
      coniveauCohomologyOpenMap k X K n a f ≫
        coniveauCohomologyToWindow k ((SmoothSite.opensFunctor X).obj U) K n a b :=
  coniveauCohomologyToWindow_restrict_naturality k K n a b ((SmoothSite.opensFunctor X).map f)

/-- Naturality of the signed boundary between actual opens. -/
theorem coniveauWindowBoundary_openMap_naturality (K : DM(k)) (n : ℤ)
    {a b : ℕ} (hab : a ≤ b) {U V : X.left.Opens} (f : U ⟶ V) :
    coniveauWindowBoundary k ((SmoothSite.opensFunctor X).obj V) K n hab ≫
        coniveauCohomologyOpenMap k X K (n + 1) b f =
      coniveauRelativeSupportOpenMap k X K n a b f ≫
        coniveauWindowBoundary k ((SmoothSite.opensFunctor X).obj U) K n hab :=
  coniveauWindowBoundary_restrict_naturality k K n hab ((SmoothSite.opensFunctor X).map f)

end AlgebraicGeometry.MotivicHomotopy
