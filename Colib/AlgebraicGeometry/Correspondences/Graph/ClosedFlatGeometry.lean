/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.FlatSingleFiber
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholeFibers
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureRelativeClosure

/-!
# Actual whole closed support pullback and its component comparisons

All maps below are literal Cartesian maps. The component comparison is built
from the actual comap ideal and native integral-component map, not from a
selected reduction of the whole pullback.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

open Scheme.PolynomialSectionPencil

variable {S X Y Z D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (m : D ⟶ pullback g h) (φ : X ⟶ Y) (hφ : φ ≫ g = f)

/-- The whole scheme-theoretic support fiber, without reduction. -/
abbrev closedSupportGraphFiber : Scheme.{u} :=
  pullback φ (m ≫ pullback.fst g h)

/-- Its outer map has the original source and final support coordinate. -/
def closedSupportGraphFiberMap : closedSupportGraphFiber g h m φ ⟶ pullback f h :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ m ≫ pullback.snd g h) (by
      rw [← hφ, ← Category.assoc, pullback.condition]
      simp only [Category.assoc]
      rw [pullback.condition])

@[reassoc (attr := simp)] theorem closedSupportGraphFiberMap_fst :
    closedSupportGraphFiberMap f g h m φ hφ ≫ pullback.fst f h = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem closedSupportGraphFiberMap_snd :
    closedSupportGraphFiberMap f g h m φ hφ ≫ pullback.snd f h =
      pullback.snd _ _ ≫ m ≫ pullback.snd g h :=
  pullback.lift_snd _ _ _

/-- The whole fiber is the actual inverse image of the original closed support. -/
theorem isPullback_closedSupportGraphFiberMap :
    IsPullback (closedSupportGraphFiberMap f g h m φ hφ) (pullback.snd _ _)
      (correspondenceGraphFiberAmbientMap f g h φ hφ) m where
  w := by
    apply pullback.hom_ext
    · simpa [correspondenceGraphFiberAmbientMap, pullback.map, Category.assoc] using
        (pullback.condition
          (f := φ) (g := m ≫ pullback.fst g h))
    · simp [correspondenceGraphFiberAmbientMap, pullback.map]
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun c => by
    have hf := congrArg (fun m => m ≫ pullback.fst g h) c.condition
    have hs := congrArg (fun m => m ≫ pullback.snd g h) c.condition
    simp only [Category.assoc, correspondenceGraphFiberAmbientMap, pullback.map,
      pullback.lift_fst, pullback.lift_snd, Category.comp_id] at hf hs
    let u := pullback.lift (c.fst ≫ pullback.fst f h) c.snd
      (by simpa only [Category.assoc] using hf)
    have hm : u ≫ closedSupportGraphFiberMap f g h m φ hφ = c.fst := by
      apply pullback.hom_ext
      · simp [u]
      · simpa [u] using hs.symm
    refine ⟨u, hm, pullback.lift_snd _ _ _, ?_⟩
    intro n hn hn'
    apply pullback.hom_ext (f := φ)
      (g := m ≫ pullback.fst g h) (k := n) (l := u)
    · simpa [u] using congrArg (fun q => q ≫ pullback.fst f h) hn
    · simpa [u] using hn')⟩

/-- The outer fiber map is a closed immersion, so no hidden residue-degree factor occurs. -/
instance closedSupportGraphFiberMap_isClosedImmersion [IsClosedImmersion m] :
    IsClosedImmersion (closedSupportGraphFiberMap f g h m φ hφ) :=
  MorphismProperty.of_isPullback
    (isPullback_closedSupportGraphFiberMap f g h m φ hφ).flip inferInstance


/-- The comap support is the entire Cartesian inverse image of an original component. -/
def closedSupportComponentFlatIso [IsClosedImmersion m] (z : D) :
    ((integralComponentAt z).comap
      (pullback.snd φ (m ≫ pullback.fst g h))).subscheme ≅
        correspondenceGraphFiber g h (m z) φ :=
  (integralComponentAt z).comapIso (pullback.snd φ (m ≫ pullback.fst g h)) ≪≫
    (wholeFiberIso (pullback.snd φ (m ≫ pullback.fst g h))
      (pullback.fst φ (m ≫ pullback.fst g h)) (m ≫ pullback.fst g h) φ
      (IsPullback.of_hasPullback φ (m ≫ pullback.fst g h)).flip
      (integralComponentAt z).subschemeι).symm ≪≫
    asIso (pullback.map φ ((integralComponentAt z).subschemeι ≫ (m ≫ pullback.fst g h))
      φ ((integralComponentAt (m z)).subschemeι ≫ pullback.fst g h)
      (𝟙 _) (integralComponentMap m z) (𝟙 _) (by simp)
      (by simp only [Category.comp_id, ← Category.assoc, integralComponentMap_subschemeι]))

/-- The component comparison preserves the actual source projection. -/
@[reassoc (attr := simp)] theorem closedSupportComponentFlatIso_fst
    [IsClosedImmersion m] (z : D) :
    (closedSupportComponentFlatIso g h m φ z).hom ≫
      pullback.fst φ ((integralComponentAt (m z)).subschemeι ≫ pullback.fst g h) =
        ((integralComponentAt z).comap
          (pullback.snd φ (m ≫ pullback.fst g h))).subschemeι ≫
            pullback.fst φ (m ≫ pullback.fst g h) := by
  let e := wholeFiberIso (pullback.snd φ (m ≫ pullback.fst g h))
    (pullback.fst φ (m ≫ pullback.fst g h)) (m ≫ pullback.fst g h) φ
    (IsPullback.of_hasPullback φ (m ≫ pullback.fst g h)).flip
    (integralComponentAt z).subschemeι
  have he : e.inv ≫ pullback.fst φ
      ((integralComponentAt z).subschemeι ≫ (m ≫ pullback.fst g h)) =
        pullback.fst _ _ ≫ pullback.fst φ (m ≫ pullback.fst g h) := by
    rw [← wholeFiberIso_hom_base (pullback.snd φ (m ≫ pullback.fst g h))
      (pullback.fst φ (m ≫ pullback.fst g h)) (m ≫ pullback.fst g h) φ
      (IsPullback.of_hasPullback φ (m ≫ pullback.fst g h)).flip
      (integralComponentAt z).subschemeι]
    simp only [e, Iso.inv_hom_id_assoc]
  simp only [closedSupportComponentFlatIso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, Category.assoc, pullback.map, pullback.lift_fst, Category.comp_id]
  rw [show (wholeFiberIso _ _ _ _ _ _).inv = e.inv from rfl, he,
    Scheme.IdealSheafData.comapIso_hom_fst_assoc]

/-- The component comparison preserves the actual original ambient inclusion. -/
@[reassoc (attr := simp)] theorem closedSupportComponentFlatIso_original
    [IsClosedImmersion m] (z : D) :
    (closedSupportComponentFlatIso g h m φ z).hom ≫
      pullback.snd φ ((integralComponentAt (m z)).subschemeι ≫ pullback.fst g h) ≫
        (integralComponentAt (m z)).subschemeι =
      ((integralComponentAt z).comap
        (pullback.snd φ (m ≫ pullback.fst g h))).subschemeι ≫
          pullback.snd φ (m ≫ pullback.fst g h) ≫ m := by
  let e := wholeFiberIso (pullback.snd φ (m ≫ pullback.fst g h))
    (pullback.fst φ (m ≫ pullback.fst g h)) (m ≫ pullback.fst g h) φ
    (IsPullback.of_hasPullback φ (m ≫ pullback.fst g h)).flip
    (integralComponentAt z).subschemeι
  have he : e.inv ≫ pullback.snd φ
      ((integralComponentAt z).subschemeι ≫ (m ≫ pullback.fst g h)) =
        pullback.snd _ _ := by
    rw [← wholeFiberIso_hom_total (pullback.snd φ (m ≫ pullback.fst g h))
      (pullback.fst φ (m ≫ pullback.fst g h)) (m ≫ pullback.fst g h) φ
      (IsPullback.of_hasPullback φ (m ≫ pullback.fst g h)).flip
      (integralComponentAt z).subschemeι]
    simp only [e, Iso.inv_hom_id_assoc]
  simp only [closedSupportComponentFlatIso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, Category.assoc, pullback.map, pullback.lift_snd,
    integralComponentMap_subschemeι]
  have he' := congrArg (fun v => v ≫ (integralComponentAt z).subschemeι ≫ m) he
  simp only [Category.assoc] at he'
  rw [show (wholeFiberIso _ _ _ _ _ _).inv = e.inv from rfl, he',
    ← pullback.condition_assoc, Scheme.IdealSheafData.comapIso_hom_fst_assoc]

/-- Both coordinates of the actual component outer map are unchanged. -/
@[reassoc (attr := simp)] theorem closedSupportComponentFlatIso_outer
    [IsClosedImmersion m] (z : D) :
    (closedSupportComponentFlatIso g h m φ z).hom ≫
      correspondenceGraphFiberMap f g h (m z) φ hφ =
        ((integralComponentAt z).comap
          (pullback.snd φ (m ≫ pullback.fst g h))).subschemeι ≫
            closedSupportGraphFiberMap f g h m φ hφ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, correspondenceGraphFiberMap_fst,
      closedSupportComponentFlatIso_fst, closedSupportGraphFiberMap_fst]
  · simp only [Category.assoc, correspondenceGraphFiberMap_snd,
      closedSupportComponentFlatIso_original_assoc, closedSupportGraphFiberMap_snd]

end Stacks.Chow
