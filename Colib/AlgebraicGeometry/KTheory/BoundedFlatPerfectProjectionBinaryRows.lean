/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumProjectionReference
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectReferenceCoherence

/-!
# Binary rows of the actual projection rectangle

The normalized source column retains the literal projection comparison after postcomposition.
The target row retains its complete precomposed reference from the total square.

Adapted from `TripleLeftColumnNodes.lean`, `TripleRightBinaryRow.lean`,
`ProjectionLeftColumn.lean`, and `NativeProjectionBinaryRows.lean` in
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectProjectionBinaryRows

open BoundedFlatPerfectReferenceCoherence (smallIso smallIso_precomp smallIso_postcomp)
local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "N" => boundedAboveFlatPerfectNormalizedPullback
local notation "NC" => boundedAboveFlatPerfectNormalizedPullbackCompIso

/-- The actual strict small model morphism of one normalized pullback. -/
def normalizedMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    asSmallCategory (W Y) ⟶ asSmallCategory (W X) :=
  asSmallCategoryMap (W Y) (W X) (boundedAboveFlatPerfectNormalizedPullback_exact f)
    (boundedAboveFlatPerfectNormalizedPullback_obj_zero _)

/-- The source, intermediate and target of binary normalization, with its two comparisons. -/
def binaryNodes {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) : Fin 3 →
    Σ F : asSmallCategory (W Z) ⟶ asSmallCategory (W X),
      (BoundedFlatPerfectBinarySimplex.sourceMap f g).hom.toFunctor ≅ F.hom.toFunctor :=
  ![⟨BoundedFlatPerfectBinarySimplex.sourceMap f g, Iso.refl _⟩,
    ⟨BoundedFlatPerfectBinarySimplex.intermediateMap f g,
      BoundedFlatPerfectBinarySimplex.first f g⟩,
    ⟨BoundedFlatPerfectBinarySimplex.targetMap f g, BoundedFlatPerfectBinarySimplex.total f g⟩]

/-- The projection rectangle indices of its three postcomposed source nodes. -/
def rectangleLeftIndex : Fin 3 → Fin 18 := ![2, 3, 11]

/-- The last triple indices of its three precomposed target nodes. -/
def rightIndex : Fin 3 → Fin 8 := ![5, 6, 7]

private theorem trans_whiskerRight_refl {A B C : Type*}
    [Category A] [Category B] [Category C] {D : A ⥤ C}
    (G : A ⥤ B) (H : B ⥤ C) (e : D ≅ G ⋙ H) :
    e = e ≪≫ isoWhiskerRight (Iso.refl G) H := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    Iso.refl_hom, NatTrans.id_app]
  have hm : H.map (𝟙 (G.obj x)) = 𝟙 (H.obj (G.obj x)) := H.map_id _
  exact ((congrArg (fun a ↦ e.hom.app x ≫ a) hm).trans
    (Category.comp_id (e.hom.app x))).symm

private theorem trans_whiskerLeft_refl {A B C : Type*}
    [Category A] [Category B] [Category C] {D : A ⥤ C}
    (G : A ⥤ B) (H : B ⥤ C) (e : D ≅ G ⋙ H) :
    e = e ≪≫ isoWhiskerLeft G (Iso.refl H) := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    Iso.refl_hom, NatTrans.id_app]
  exact (Category.comp_id (e.hom.app x)).symm

section TripleRows

variable {X Y Z T : Scheme.{u}} (F : asSmallCategory (W T) ⟶ asSmallCategory (W X))
  (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- The same original binary column after literal normalized postcomposition. -/
def binaryColumnNode
    (e : F.hom.toFunctor = (BoundedFlatPerfectTripleSimplex.source f g h).hom.toFunctor)
    (i : Fin 3) : Σ G : asSmallCategory (W T) ⟶ asSmallCategory (W X),
    F.hom.toFunctor ≅ G.hom.toFunctor :=
  ⟨(binaryNodes g h i).1 ≫ normalizedMap f,
    (eqToIso e ≪≫ BoundedFlatPerfectBinarySimplex.total f (g ≫ h)) ≪≫
      isoWhiskerRight (binaryNodes g h i).2 (normalizedMap f).hom.toFunctor⟩

/-- The original right row starts with the actual normalized comparison. -/
def rightRowReference
    (ρ : F.hom.toFunctor ≅ (BoundedFlatPerfectTripleSimplex.source f g h).hom.toFunctor) :
    F.hom.toFunctor ≅
      (normalizedMap h ≫ BoundedFlatPerfectBinarySimplex.sourceMap f g).hom.toFunctor :=
  ρ ≪≫ BoundedFlatPerfectTripleSimplex.rightFirst f g h

/-- The same original binary row after literal normalized precomposition. -/
def preBinaryNodes (P : asSmallCategory (W T) ⟶ asSmallCategory (W Z))
    (b : X ⟶ Y) (c : Y ⟶ Z)
    (ρ : F.hom.toFunctor ≅ (P ≫ BoundedFlatPerfectBinarySimplex.sourceMap b c).hom.toFunctor)
    (i : Fin 3) : Σ G : asSmallCategory (W T) ⟶ asSmallCategory (W X),
    F.hom.toFunctor ≅ G.hom.toFunctor :=
  ⟨P ≫ (binaryNodes b c i).1,
    ρ ≪≫ isoWhiskerLeft P.hom.toFunctor (binaryNodes b c i).2⟩

/-- The full left split-triple node at each binary postcomposition index. -/
def tripleLeftNode
    (e : F.hom.toFunctor = (BoundedFlatPerfectTripleSimplex.source f g h).hom.toFunctor)
    (i : Fin 3) : Σ G : asSmallCategory (W T) ⟶ asSmallCategory (W X),
    F.hom.toFunctor ≅ G.hom.toFunctor :=
  ⟨BoundedFlatPerfectSplitTripleSimplex.vertices f g h (![2, 3, 7] i),
    eqToIso e ≪≫ BoundedFlatPerfectSplitTripleSimplex.references f g h (![2, 3, 7] i)⟩

/-- The selected left column retains the entire original comparison after postcomposition. -/
theorem triple_left_column
    (e : F.hom.toFunctor = (BoundedFlatPerfectTripleSimplex.source f g h).hom.toFunctor)
    (i : Fin 3) : tripleLeftNode F f g h e i = binaryColumnNode F f g h e i := by
  have hm (j : Fin 3) : (tripleLeftNode F f g h e j).1 =
      (binaryColumnNode F f g h e j).1 := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    fin_cases j <;> rfl
  fin_cases i
  · apply Sigma.ext (hm 0)
    apply heq_of_eq
    change eqToIso e ≪≫ BoundedFlatPerfectBinarySimplex.total f (g ≫ h) =
      (eqToIso e ≪≫ BoundedFlatPerfectBinarySimplex.total f (g ≫ h)) ≪≫
        isoWhiskerRight (Iso.refl (BoundedFlatPerfectBinarySimplex.sourceMap g h).hom.toFunctor)
          (normalizedMap f).hom.toFunctor
    exact trans_whiskerRight_refl
      (BoundedFlatPerfectBinarySimplex.sourceMap g h).hom.toFunctor
      (normalizedMap f).hom.toFunctor
      (eqToIso e ≪≫ BoundedFlatPerfectBinarySimplex.total f (g ≫ h))
  · apply Sigma.ext (hm 1)
    apply heq_of_eq
    change eqToIso e ≪≫ (smallIso (NC f (g ≫ h)) ≪≫
        smallIso (isoWhiskerRight (BoundedFlatPerfectBinarySimplex.geometricIso g h) (N f))) =
      (eqToIso e ≪≫ smallIso (NC f (g ≫ h))) ≪≫
        isoWhiskerRight (smallIso (BoundedFlatPerfectBinarySimplex.geometricIso g h))
          (AsSmall.down ⋙ N f ⋙ AsSmall.up)
    rw [smallIso_postcomp, Iso.trans_assoc]
  · apply Sigma.ext (hm 2)
    apply heq_of_eq
    have ha : Functor.associator (N h) (N g) (N f) = Iso.refl _ := rfl
    change eqToIso e ≪≫ (smallIso (NC f (g ≫ h)) ≪≫
        smallIso (isoWhiskerRight (NC g h) (N f) ≪≫
          Functor.associator (N h) (N g) (N f))) =
      (eqToIso e ≪≫ smallIso (NC f (g ≫ h))) ≪≫
        isoWhiskerRight (smallIso (NC g h)) (AsSmall.down ⋙ N f ⋙ AsSmall.up)
    rw [ha, Iso.trans_refl, smallIso_postcomp, Iso.trans_assoc]

/-- The full right split-triple node at each binary precomposition index. -/
def tripleRightNode
    (ρ : F.hom.toFunctor ≅ (BoundedFlatPerfectTripleSimplex.source f g h).hom.toFunctor)
    (i : Fin 3) : Σ G : asSmallCategory (W T) ⟶ asSmallCategory (W X),
    F.hom.toFunctor ≅ G.hom.toFunctor :=
  ⟨BoundedFlatPerfectSplitTripleSimplex.vertices f g h (rightIndex i),
    ρ ≪≫ BoundedFlatPerfectSplitTripleSimplex.references f g h (rightIndex i)⟩

/-- The selected right row retains the entire original comparison after precomposition. -/
theorem triple_right_row
    (ρ : F.hom.toFunctor ≅ (BoundedFlatPerfectTripleSimplex.source f g h).hom.toFunctor)
    (i : Fin 3) : tripleRightNode F f g h ρ i =
      preBinaryNodes F (normalizedMap h) f g (rightRowReference F f g h ρ) i := by
  have hm (j : Fin 3) : (tripleRightNode F f g h ρ j).1 =
      (preBinaryNodes F (normalizedMap h) f g (rightRowReference F f g h ρ) j).1 := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    fin_cases j <;> rfl
  fin_cases i
  · apply Sigma.ext (hm 0)
    apply heq_of_eq
    change ρ ≪≫ BoundedFlatPerfectTripleSimplex.rightFirst f g h =
      (ρ ≪≫ BoundedFlatPerfectTripleSimplex.rightFirst f g h) ≪≫
        isoWhiskerLeft (normalizedMap h).hom.toFunctor
          (Iso.refl (BoundedFlatPerfectBinarySimplex.sourceMap f g).hom.toFunctor)
    exact trans_whiskerLeft_refl (normalizedMap h).hom.toFunctor
      (BoundedFlatPerfectBinarySimplex.sourceMap f g).hom.toFunctor
      (ρ ≪≫ BoundedFlatPerfectTripleSimplex.rightFirst f g h)
  · apply Sigma.ext (hm 1)
    apply heq_of_eq
    change ρ ≪≫ (BoundedFlatPerfectTripleSimplex.rightFirst f g h ≪≫
        smallIso (isoWhiskerLeft (N h) (BoundedFlatPerfectBinarySimplex.geometricIso f g))) =
      (ρ ≪≫ BoundedFlatPerfectTripleSimplex.rightFirst f g h) ≪≫
        isoWhiskerLeft (AsSmall.down ⋙ N h ⋙ AsSmall.up)
          (smallIso (BoundedFlatPerfectBinarySimplex.geometricIso f g))
    rw [smallIso_precomp, Iso.trans_assoc]
  · apply Sigma.ext (hm 2)
    apply heq_of_eq
    have he : BoundedFlatPerfectTripleSimplex.leftFirst f g h ≪≫
        BoundedFlatPerfectTripleSimplex.leftSecond f g h =
        BoundedFlatPerfectTripleSimplex.rightFirst f g h ≪≫
          BoundedFlatPerfectTripleSimplex.rightSecond f g h :=
      Iso.ext (BoundedFlatPerfectTripleSimplex.two_routes f g h)
    change ρ ≪≫ (BoundedFlatPerfectTripleSimplex.leftFirst f g h ≪≫
      BoundedFlatPerfectTripleSimplex.leftSecond f g h) = _
    rw [he]
    change ρ ≪≫ (BoundedFlatPerfectTripleSimplex.rightFirst f g h ≪≫
        smallIso (isoWhiskerLeft (N h) (NC f g))) =
      (ρ ≪≫ BoundedFlatPerfectTripleSimplex.rightFirst f g h) ≪≫
        isoWhiskerLeft (AsSmall.down ⋙ N h ⋙ AsSmall.up) (smallIso (NC f g))
    rw [smallIso_precomp, Iso.trans_assoc]

end TripleRows

variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (r : C ⟶ A) (hr : q ≫ p = r)

/-- The complete original source binary column, with its literal projection anchor. -/
theorem native_source_column (i : Fin 3) :
    BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr (rectangleLeftIndex i) =
      binaryColumnNode (BoundedFlatPerfectProjectionReference.reference c r) c q p
        (BoundedFlatPerfectProjectionReference.anchor p q c r hr) i := by
  have h : BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr
      (rectangleLeftIndex i) =
      tripleLeftNode (BoundedFlatPerfectProjectionReference.reference c r) c q p
        (BoundedFlatPerfectProjectionReference.anchor p q c r hr) i := by
    fin_cases i <;> rfl
  exact h.trans (triple_left_column _ _ _ _ _ _)

/-- The reference from the projection anchor to the last normalized triple. -/
def nativeLastReference : (BoundedFlatPerfectProjectionReference.reference c r).hom.toFunctor ≅
    (BoundedFlatPerfectTripleSimplex.source q' p' a).hom.toFunctor :=
  eqToIso (BoundedFlatPerfectProjectionReference.anchor p q c r hr) ≪≫
    BoundedFlatPerfectDoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq

/-- Each last-triple node keeps the exact square-induced reference. -/
theorem native_last_nodes (i : Fin 8) :
    BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr
      (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom i) =
    (⟨BoundedFlatPerfectSplitTripleSimplex.vertices q' p' a i,
      nativeLastReference p q p' q' a b c hp hq r hr ≪≫
        BoundedFlatPerfectSplitTripleSimplex.references q' p' a i⟩ :
        BoundedFlatPerfectProjectionReference.Node c r) := by
  let η := eqToIso (BoundedFlatPerfectProjectionReference.anchor p q c r hr)
  let M := BoundedFlatPerfectDoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq
    (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom i)
  let T := BoundedFlatPerfectDoubleSquareCommonSimplex.lastSourceIso p q p' q' a b c hp hq
  have hm : M = ⟨BoundedFlatPerfectSplitTripleSimplex.vertices q' p' a i,
      T ≪≫ BoundedFlatPerfectSplitTripleSimplex.references q' p' a i⟩ :=
    (BoundedFlatPerfectDoubleSquareMergedSimplex.last_nodes p q p' q' a b c hp hq i).trans
      (BoundedFlatPerfectDoubleSquareCommonSimplex.last_nodes p q p' q' a b c hp hq i)
  change (⟨M.1, η ≪≫ M.2⟩ : BoundedFlatPerfectProjectionReference.Node c r) = _
  rw [hm]
  change (⟨BoundedFlatPerfectSplitTripleSimplex.vertices q' p' a i,
      η ≪≫ (T ≪≫ BoundedFlatPerfectSplitTripleSimplex.references q' p' a i)⟩ :
    BoundedFlatPerfectProjectionReference.Node c r) =
      ⟨BoundedFlatPerfectSplitTripleSimplex.vertices q' p' a i,
      (η ≪≫ T) ≪≫ BoundedFlatPerfectSplitTripleSimplex.references q' p' a i⟩
  rw [Iso.trans_assoc]

/-- The entire target projection row retains both original normalization pieces. -/
theorem native_target_row (i : Fin 3) :
    BoundedFlatPerfectProjectionReference.nodes p q p' q' a b c hp hq r hr
      (BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) =
    preBinaryNodes (BoundedFlatPerfectProjectionReference.reference c r) (normalizedMap a) q' p'
      (rightRowReference (BoundedFlatPerfectProjectionReference.reference c r) q' p' a
        (nativeLastReference p q p' q' a b c hp hq r hr)) i :=
  (native_last_nodes p q p' q' a b c hp hq r hr (rightIndex i)).trans
    (triple_right_row (BoundedFlatPerfectProjectionReference.reference c r) q' p' a
      (nativeLastReference p q p' q' a b c hp hq r hr) i)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectProjectionBinaryRows
