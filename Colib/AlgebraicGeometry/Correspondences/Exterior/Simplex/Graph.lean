/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.Correspondences.Exterior.Simplex.Basic
public import Colib.AlgebraicGeometry.Correspondences.Graph.Functor

/-!
# Exterior extension of actual graph correspondences

The product projection identifies the irreducible components of the source
with those of its product with the simplex. On each component, the exterior
support is the graph of the literal product map. Reindexing the native prime
sum proves preservation of graph correspondences and hence identities.

This adapts the argument of
`Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/Graph.lean`
at commit `a6805c4a87cdfd7717dd7a94039246a167f15380` to native point-indexed cycles.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

private theorem point_eq_of_projection_graph
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (φ : X ⟶ Y) (hφ : φ ≫ g = f) (a b : pullback (C := Scheme) f g)
    (ha : (integralComponentAt a).subschemeι ≫ pullback.fst f g ≫ φ =
      (integralComponentAt a).subschemeι ≫ pullback.snd f g)
    (hb : (integralComponentAt b).subschemeι ≫ pullback.fst f g ≫ φ =
      (integralComponentAt b).subschemeι ≫ pullback.snd f g)
    (hr : Set.range ((integralComponentAt a).subschemeι ≫ pullback.fst f g) =
      Set.range ((integralComponentAt b).subschemeι ≫ pullback.fst f g)) : a = b := by
  have hi (t : pullback (C := Scheme) f g)
      (ht : (integralComponentAt t).subschemeι ≫ pullback.fst f g ≫ φ =
        (integralComponentAt t).subschemeι ≫ pullback.snd f g) :
      (integralComponentAt t).subschemeι =
        ((integralComponentAt t).subschemeι ≫ pullback.fst f g) ≫
          correspondenceGraphMap f g φ hφ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, correspondenceGraphMap_fst, Category.comp_id]
    · simpa only [Category.assoc, correspondenceGraphMap_snd] using ht.symm
  have hr' : Set.range (integralComponentAt a).subschemeι =
      Set.range (integralComponentAt b).subschemeι := by
    rw [hi a ha, hi b hb]
    change Set.range (correspondenceGraphMap f g φ hφ ∘
      ((integralComponentAt a).subschemeι ≫ pullback.fst f g)) =
      Set.range (correspondenceGraphMap f g φ hφ ∘
        ((integralComponentAt b).subschemeι ≫ pullback.fst f g))
    rw [Set.range_comp, Set.range_comp, hr]
  have hc : closure ({a} : Set (pullback (C := Scheme) f g)) = closure {b} := by
    simpa only [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt] using hr'
  have hg : IsGenericPoint a (closure ({b} : Set (pullback (C := Scheme) f g))) :=
    hc ▸ isGenericPoint_closure
  exact hg.eq isGenericPoint_closure

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}

/-- Generic source points correspond to generic points after adjoining the simplex. -/
def simplexGenericPointEquiv (X : SmoothSite (Spec (.of k))) (n : ℕ) :
    genericPoints X.left ≃
      genericPoints (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).left :=
  (genericPoints.equiv (α := X.left)).trans
    (((pullback.fst X.hom (AlgebraicSimplex.smoothSiteObj k n).hom).irreducibleComponentsEquiv
      (pullback.fst X.hom (AlgebraicSimplex.smoothSiteObj k n).hom).isOpenMap).symm.trans
      (genericPoints.equiv
        (α := (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).left)).symm)

/-- The corresponding component is precisely the inverse image of the original component. -/
theorem simplexGenericPointEquiv_closure (X : SmoothSite (Spec (.of k))) (n : ℕ)
    (t : genericPoints X.left) :
    closure ({(simplexGenericPointEquiv X n t).val} :
      Set (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).left) =
      (pullback.fst X.hom (AlgebraicSimplex.smoothSiteObj k n).hom) ⁻¹' closure {t.val} := by
  change (genericPoints.component (genericPoints.ofComponent
    (((pullback.fst X.hom (AlgebraicSimplex.smoothSiteObj k n).hom).irreducibleComponentsEquiv
      (pullback.fst X.hom (AlgebraicSimplex.smoothSiteObj k n).hom).isOpenMap).symm
        (genericPoints.component t)))).val = _
  rw [genericPoints.component_ofComponent]
  rfl

/-- The native exterior component projects onto the product of the original source component. -/
theorem range_integralComponentAt_simplexExteriorPoint_fst
    (z : pullback (C := Scheme) X.hom Y.hom) (n : ℕ)
    (hz : IsFiniteCorrespondencePoint X.hom Y.hom z) :
    @Eq (Set (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).left)
      (Set.range ((integralComponentAt (simplexExteriorPoint z n hz)).subschemeι ≫
        pullback.fst (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
          (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom))
      ((pullback.fst X.hom (AlgebraicSimplex.smoothSiteObj k n).hom) ⁻¹'
        Set.range ((integralComponentAt z).subschemeι ≫ pullback.fst X.hom Y.hom)) := by
  rw [integralComponentAt_simplexExteriorPoint]
  let e := simplexExteriorInclusion z n
  let p : pullback (C := Scheme)
      (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
      (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom ⟶
        (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).left :=
    pullback.fst _ _
  let : IsClosedImmersion e := simplexExteriorInclusion_isClosedImmersion z n hz
  have he : e.toImage ≫ e.imageι ≫ p = simplexExteriorSource z n := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    exact simplexExteriorInclusion_fst z n
  change Set.range (e.imageι ≫ p) = _
  calc
    Set.range (e.imageι ≫ p) = Set.range (e.toImage ≫ e.imageι ≫ p) :=
      (e.toImage.surjective.range_comp (e.imageι ≫ p)).symm
    _ = Set.range (simplexExteriorSource z n) := by rw [he]
    _ = _ := simplexExteriorSource_range z n

/-- An original graph relation becomes the graph relation for the literal product map. -/
theorem simplexExteriorPoint_projection_graph (n : ℕ) (φ : X ⟶ Y)
    (z : pullback (C := Scheme) X.hom Y.hom)
    (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
    (hφ : (integralComponentAt z).subschemeι ≫ pullback.fst X.hom Y.hom ≫ φ.left =
      (integralComponentAt z).subschemeι ≫ pullback.snd X.hom Y.hom) :
    (integralComponentAt (simplexExteriorPoint z n hz)).subschemeι ≫
        pullback.fst (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
          (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom ≫
            (SmoothSite.productMap φ (𝟙 (AlgebraicSimplex.smoothSiteObj k n))).left =
      (integralComponentAt (simplexExteriorPoint z n hz)).subschemeι ≫
        pullback.snd (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
          (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom := by
  rw [integralComponentAt_simplexExteriorPoint]
  let e := simplexExteriorInclusion z n
  let : IsClosedImmersion e := simplexExteriorInclusion_isClosedImmersion z n hz
  apply (cancel_epi e.toImage).mp
  change e.toImage ≫ e.imageι ≫
      pullback.fst (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
        (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom ≫
          (SmoothSite.productMap φ (𝟙 (AlgebraicSimplex.smoothSiteObj k n))).left =
    e.toImage ≫ e.imageι ≫
      pullback.snd (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
        (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom
  simp only [← Category.assoc, Scheme.Hom.toImage_imageι]
  dsimp only [e]
  rw [simplexExteriorInclusion_fst, simplexExteriorInclusion_snd]
  have hf := congrArg (fun a => a.left)
    (SmoothSite.productMap_fst φ (𝟙 (AlgebraicSimplex.smoothSiteObj k n)))
  have hs := congrArg (fun a => a.left)
    (SmoothSite.productMap_snd φ (𝟙 (AlgebraicSimplex.smoothSiteObj k n)))
  change (SmoothSite.productMap φ (𝟙 (AlgebraicSimplex.smoothSiteObj k n))).left ≫
    pullback.fst Y.hom (AlgebraicSimplex.smoothSiteObj k n).hom =
      pullback.fst X.hom (AlgebraicSimplex.smoothSiteObj k n).hom ≫ φ.left at hf
  change (SmoothSite.productMap φ (𝟙 (AlgebraicSimplex.smoothSiteObj k n))).left ≫
    pullback.snd Y.hom (AlgebraicSimplex.smoothSiteObj k n).hom =
      pullback.snd X.hom (AlgebraicSimplex.smoothSiteObj k n).hom ≫ 𝟙 _ at hs
  apply pullback.hom_ext
  · simp only [Category.assoc, hf, simplexExteriorSource_fst_assoc,
      hφ, simplexExteriorTarget_fst]
  · simp only [Category.assoc, hs, Category.comp_id,
      simplexExteriorSource_snd, simplexExteriorTarget_snd]

/-- A prime graph component extends to the corresponding prime of the product graph. -/
theorem simplexExteriorPoint_graphMap (n : ℕ) (φ : X ⟶ Y) (t : genericPoints X.left) :
    simplexExteriorPoint (correspondenceGraphMap X.hom Y.hom φ.left
      (MorphismProperty.Over.w φ) t.val) n
      (isFiniteCorrespondencePoint_graphMap X.hom Y.hom φ.left
        (MorphismProperty.Over.w φ) t) =
      correspondenceGraphMap (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
        (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom
        (SmoothSite.productMap φ (𝟙 (AlgebraicSimplex.smoothSiteObj k n))).left
        (MorphismProperty.Over.w _) (simplexGenericPointEquiv X n t).val := by
  apply point_eq_of_projection_graph
    (X := (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).left)
    (Y := (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).left)
    (S := Spec (.of k)) _ _
    (SmoothSite.productMap φ (𝟙 (AlgebraicSimplex.smoothSiteObj k n))).left
    (MorphismProperty.Over.w _)
  · apply simplexExteriorPoint_projection_graph
    exact (integralComponentAt_graphMap_snd _ _ _ _ _).symm
  · exact (integralComponentAt_graphMap_snd _ _ _ _ _).symm
  · calc
      _ = (pullback.fst X.hom (AlgebraicSimplex.smoothSiteObj k n).hom) ⁻¹'
          Set.range ((integralComponentAt (correspondenceGraphMap X.hom Y.hom φ.left
            (MorphismProperty.Over.w φ) t.val)).subschemeι ≫ pullback.fst X.hom Y.hom) :=
        range_integralComponentAt_simplexExteriorPoint_fst (X := X) (Y := Y)
          (correspondenceGraphMap X.hom Y.hom φ.left (MorphismProperty.Over.w φ) t.val) n
          (isFiniteCorrespondencePoint_graphMap X.hom Y.hom φ.left
            (MorphismProperty.Over.w φ) t)
      _ = (pullback.fst X.hom (AlgebraicSimplex.smoothSiteObj k n).hom) ⁻¹' closure {t.val} :=
        congrArg (fun C : Set X.left =>
          (pullback.fst X.hom (AlgebraicSimplex.smoothSiteObj k n).hom) ⁻¹' C)
          (range_integralComponentAt_graphMap_fst X.hom Y.hom φ.left
            (MorphismProperty.Over.w φ) t.val)
      _ = closure {(simplexGenericPointEquiv X n t).val} :=
        (simplexGenericPointEquiv_closure X n t).symm
      _ = _ := (range_integralComponentAt_graphMap_fst
        (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
        (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom
        (SmoothSite.productMap φ (𝟙 (AlgebraicSimplex.smoothSiteObj k n))).left
        (MorphismProperty.Over.w _) (simplexGenericPointEquiv X n t).val).symm

/-- Exterior extension preserves the full native graph sum, including empty sources. -/
theorem simplexExterior_graphCorrespondence (n : ℕ) (φ : X ⟶ Y)
    (hX : (genericPoints X.left).Finite)
    (hXT : (genericPoints
      (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).left).Finite) :
    @Eq (finiteCorrespondences
      (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
      (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom)
      (simplexExterior (X := X) (Y := Y) n
        (graphCorrespondenceOfComponents X.hom Y.hom φ.left (MorphismProperty.Over.w φ) hX))
      (graphCorrespondenceOfComponents
        (SmoothSite.product X (AlgebraicSimplex.smoothSiteObj k n)).hom
        (SmoothSite.product Y (AlgebraicSimplex.smoothSiteObj k n)).hom
        (SmoothSite.productMap φ (𝟙 (AlgebraicSimplex.smoothSiteObj k n))).left
        (MorphismProperty.Over.w _) hXT) := by
  classical
  let := hX.fintype
  let := hXT.fintype
  rw [graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence,
    graphCorrespondenceOfComponents_eq_sum_singleFiniteCorrespondence, map_sum]
  apply Fintype.sum_equiv (simplexGenericPointEquiv X n)
  intro t
  rw [simplexExterior_single]
  congr 1
  exact simplexExteriorPoint_graphMap n φ t

end Stacks.Chow

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]

/-- Exterior multiplication by the simplex preserves graphs of arbitrary smooth-site maps. -/
theorem simplexExterior_graph (n : ℕ)
    {X Y : SmoothSite (Spec (.of k))} (φ : X ⟶ Y) :
    simplexExterior n ((graphFunctor k).map φ) =
      (graphFunctor k).map
        (SmoothSite.productMap φ (𝟙 (AlgebraicSimplex.smoothSiteObj k n))) :=
  Stacks.Chow.simplexExterior_graphCorrespondence n φ _ _

/-- The actual componentwise diagonal identity is preserved in every simplex degree. -/
@[simp]
theorem simplexExterior_id (n : ℕ) (X : Cor k) :
    simplexExterior n (𝟙 X) = 𝟙 (simplexProduct X n) := by
  cases X with
  | mk U =>
    change simplexExterior n ((graphFunctor k).map (𝟙 U)) =
      (graphFunctor k).map (𝟙 (SmoothSite.product U (AlgebraicSimplex.smoothSiteObj k n)))
    rw [simplexExterior_graph, SmoothSite.productMap_id]

end AlgebraicGeometry.Cor

attribute [colib_tag "COL-0394"]
  AlgebraicGeometry.Cor.simplexExterior_graph
  AlgebraicGeometry.Cor.simplexExterior_id

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/Graph.lean:231-244" "adaptation"
  "The graph equation in the native signed correspondence groups"]
  AlgebraicGeometry.Cor.simplexExterior_graph
