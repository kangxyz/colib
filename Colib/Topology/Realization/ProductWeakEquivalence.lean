/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.MorphismProperty
public import Colib.Topology.Realization.ProductComparison
import Colib.Topology.Homotopy.HomotopyGroup.ProductWeakEquivalence

/-!
# Weak equivalences of products of simplicial sets

The original comparison from a realized product to the topological product
has exact compact lifts and is injective. These facts also give component
surjectivity and degree-zero homotopy-set bijectivity. Naturality of the
comparison proves the product weak-equivalence property for the actual
simplicial product maps.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Topology
open scoped Simplicial Topology

universe u

namespace SSet.ProductRealization

/-- The original realization-product comparison is a weak homotopy equivalence. -/
theorem comparison_isWeakHomotopyEquivalence (X Y : SSet.{u}) :
    IsWeakHomotopyEquivalence (comparison X Y) where
  component_surjective y := by
    obtain ⟨g, hg⟩ := comparison_compact_lifts X Y Unit (ContinuousMap.const Unit y)
    have hy : comparison X Y (g ()) = y := ContinuousMap.congr_fun hg ()
    refine ⟨g (), ⟨?_⟩⟩
    rw [hy]
  homotopy_bijective x n :=
    homotopyGroupMap_bijective_of_compact_lifts (comparison X Y) (comparison_injective X Y)
      (comparison_compact_lifts X Y) x n

end SSet.ProductRealization

namespace SSet.IsRealizationWeakEquivalence

/-- The tensor of two realization weak equivalences is a realization weak equivalence. -/
theorem tensorHom {X X' Y Y' : SSet.{u}} {f : X ⟶ X'} {g : Y ⟶ Y'}
    (hf : IsRealizationWeakEquivalence f) (hg : IsRealizationWeakEquivalence g) :
    IsRealizationWeakEquivalence (f ⊗ₘ g) := by
  let p := ProductRealization.comparison X Y
  let q := ProductRealization.comparison X' Y'
  let F := (SSet.toTop.map f).hom
  let G := (SSet.toTop.map g).hom
  have hf' : IsWeakHomotopyEquivalence F := hf
  have hg' : IsWeakHomotopyEquivalence G := hg
  have h : IsWeakHomotopyEquivalence ((F.prodMap G).comp p) :=
    (hf'.prodMap hg').comp (ProductRealization.comparison_isWeakHomotopyEquivalence X Y)
  have e : q.comp (SSet.toTop.map (f ⊗ₘ g)).hom = (F.prodMap G).comp p :=
    congrArg TopCat.Hom.hom (CartesianMonoidalCategory.prodComparison_natural SSet.toTop f g)
  rw [← e] at h
  exact h.of_comp_right (ProductRealization.comparison_isWeakHomotopyEquivalence X' Y')

private def prodTensorIso (X Y : SSet.{u}) : X ⨯ Y ≅ X ⊗ Y :=
  (limit.isLimit (pair X Y)).conePointUniqueUpToIso (tensorProductIsBinaryProduct X Y)

@[reassoc (attr := simp)]
private theorem prodTensorIso_hom_fst (X Y : SSet.{u}) :
    (prodTensorIso X Y).hom ≫ fst X Y = prod.fst :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (⟨WalkingPair.left⟩ : Discrete WalkingPair)

@[reassoc (attr := simp)]
private theorem prodTensorIso_hom_snd (X Y : SSet.{u}) :
    (prodTensorIso X Y).hom ≫ snd X Y = prod.snd :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (⟨WalkingPair.right⟩ : Discrete WalkingPair)

/-- The literal categorical product of realization weak equivalences is weak. -/
theorem prodMap {X X' Y Y' : SSet.{u}} {f : X ⟶ X'} {g : Y ⟶ Y'}
    (hf : IsRealizationWeakEquivalence f) (hg : IsRealizationWeakEquivalence g) :
    IsRealizationWeakEquivalence (prod.map f g) := by
  refine of_iso_square _ _ (prodTensorIso X Y) (prodTensorIso X' Y') ?_ (hf.tensorHom hg)
  apply CartesianMonoidalCategory.hom_ext <;> simp [Category.assoc]

end SSet.IsRealizationWeakEquivalence
