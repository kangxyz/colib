/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import StacksFrontier.Homology.DerivedIndexing.Extend

/-! # Extension of a parameter comparison square

The comparison is an arbitrary natural transformation between the original
composite additive functors. It is not assumed invertible. Extension uses the
native `mapExtendIso` and does not replace any complex or parameter map.

The composition lemma is extracted, with the same component proof, from
`SheavesWithTransfers/TorusSheafification/DerivedComparison/SingularPlacement.lean`.
That file's private helper was already generic in the coefficient categories,
functors, complex shapes and embedding. The transport proof follows its `hτ`
argument but allows arbitrary source and target comparison morphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Stacks.DerivedIndexing

/-- The native extension comparison for a composite is the composite of the
native extension comparisons. Extracted from the existing singular-placement proof. -/
theorem mapExtendIso_hom_comp
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    [HasZeroObject A] [HasZeroObject B] [HasZeroObject C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (K : HomologicalComplex A c) :
    (mapExtendIso (F ⋙ G) e K).hom =
      (mapExtendIso G e ((F.mapHomologicalComplex c).obj K)).hom ≫
        (G.mapHomologicalComplex c').map (mapExtendIso F e K).hom := by
  ext i' : 1
  change (mapExtendXIso (F ⋙ G) K (e.r i')).hom =
    (mapExtendXIso G ((F.mapHomologicalComplex c).obj K) (e.r i')).hom ≫
      G.map ((mapExtendXIso F K (e.r i')).hom)
  generalize e.r i' = j
  cases j with
  | none => exact (HomologicalComplex.extend.isZero_X _ rfl).eq_of_src _ _
  | some j =>
    simp only [mapExtendXIso, Iso.refl_hom, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl

variable {C D : Type*} [Category C] [Category D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  (E : C ⥤ D) (F : C ⥤ C) (G : D ⥤ D)
  [E.Additive] [F.Additive] [G.Additive] (τ : F ⋙ E ⟶ E ⋙ G)
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (e : c.Embedding c')
  {M N : HomologicalComplex C c} {M' N' : HomologicalComplex D c}
  (f : M ⟶ (F.mapHomologicalComplex c).obj N)
  (g : M' ⟶ (G.mapHomologicalComplex c).obj N')
  (a : (E.mapHomologicalComplex c).obj M ⟶ M')
  (b : (E.mapHomologicalComplex c).obj N ⟶ N')

/-- Extending a genuine parameter square preserves its original maps and its
one-way comparison. Even the source and target comparison maps need not be isomorphisms. -/
theorem parameterSquare_extend
    (h : (E.mapHomologicalComplex c).map f ≫
      (NatTrans.mapHomologicalComplex τ c).app N ≫
        (G.mapHomologicalComplex c).map b = a ≫ g) :
    (E.mapHomologicalComplex c').map
        ((e.extendFunctor C).map f ≫ (mapExtendIso F e N).hom) ≫
      (NatTrans.mapHomologicalComplex τ c').app (N.extend e) ≫
      (G.mapHomologicalComplex c').map
        ((mapExtendIso E e N).inv ≫ (e.extendFunctor D).map b) =
    ((mapExtendIso E e M).inv ≫ (e.extendFunctor D).map a) ≫
      (e.extendFunctor D).map g ≫ (mapExtendIso G e N').hom := by
  let E₀ := E.mapHomologicalComplex c
  let E₁ := E.mapHomologicalComplex c'
  let G₀ := G.mapHomologicalComplex c
  let G₁ := G.mapHomologicalComplex c'
  let X := e.extendFunctor C
  let Y := e.extendFunctor D
  let aM := mapExtendIso E e M
  let aN := mapExtendIso E e N
  let aFN := mapExtendIso E e ((F.mapHomologicalComplex c).obj N)
  let bN := mapExtendIso F e N
  let cN := mapExtendIso G e (E₀.obj N)
  let cN' := mapExtendIso G e N'
  let τ₀ := (NatTrans.mapHomologicalComplex τ c).app N
  let τ₁ := (NatTrans.mapHomologicalComplex τ c').app (N.extend e)
  have hf : E₁.map (X.map f) = aM.inv ≫ Y.map (E₀.map f) ≫ aFN.hom := by
    have hh := congrArg (fun z => z ≫ aFN.hom)
      ((mapExtendNatIso E e).inv.naturality f)
    change (E₁.map (X.map f) ≫ aFN.inv) ≫ aFN.hom =
      (aM.inv ≫ Y.map (E₀.map f)) ≫ aFN.hom at hh
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hh
  have hτ : Y.map τ₀ ≫ cN.hom ≫ G₁.map aN.hom =
      aFN.hom ≫ E₁.map bN.hom ≫ τ₁ := by
    have hh := mapExtendIso_hom_natTrans τ e N
    simpa only [mapExtendIso_hom_comp, Category.assoc] using hh
  have hb : Y.map (G₀.map b) ≫ cN'.hom = cN.hom ≫ G₁.map (Y.map b) :=
    (mapExtendNatIso G e).hom.naturality b
  have hcancel : G₁.map aN.hom ≫ G₁.map aN.inv = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  change E₁.map (X.map f ≫ bN.hom) ≫ τ₁ ≫
      G₁.map (aN.inv ≫ Y.map b) =
    (aM.inv ≫ Y.map a) ≫ Y.map g ≫ cN'.hom
  calc
    _ = (aM.inv ≫ Y.map (E₀.map f)) ≫
        (aFN.hom ≫ E₁.map bN.hom ≫ τ₁) ≫ G₁.map (aN.inv ≫ Y.map b) := by
      simp only [Functor.map_comp, hf, Category.assoc]
    _ = (aM.inv ≫ Y.map (E₀.map f)) ≫
        (Y.map τ₀ ≫ cN.hom ≫ G₁.map aN.hom) ≫ G₁.map (aN.inv ≫ Y.map b) := by
      rw [hτ]
    _ = aM.inv ≫ Y.map (E₀.map f) ≫ Y.map τ₀ ≫
        cN.hom ≫ G₁.map (Y.map b) := by
      simp only [Functor.map_comp, Category.assoc]
      rw [reassoc_of% hcancel]
    _ = aM.inv ≫ Y.map (E₀.map f) ≫ Y.map τ₀ ≫ Y.map (G₀.map b) ≫ cN'.hom := by
      rw [← hb]
    _ = aM.inv ≫ Y.map (E₀.map f ≫ τ₀ ≫ G₀.map b) ≫ cN'.hom := by
      simp only [Functor.map_comp, Category.assoc]
    _ = aM.inv ≫ Y.map (a ≫ g) ≫ cN'.hom := by rw [h]
    _ = _ := by simp only [Functor.map_comp, Category.assoc]

end Stacks.DerivedIndexing
