/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.SnakeMap
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Exact functors and the native homology-sequence boundary

The comparison uses the original native homology, cycle and opcycle
isomorphisms. Their compatibility with the structure maps gives an actual
morphism of native snake inputs. Snake naturality and `SnakeInput.map_δ`
then prove compatibility of the connecting morphisms, for every complex
shape. No change from chain to cochain indexing or passage to a derived
category is made.

The native input is the homology sequence (Stacks Tag 0111), and the native
homology-preservation comparisons in Mathlib. This is a direct categorical
compatibility theorem, not a new homology model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u₂ v₂ u₃

namespace CategoryTheory.ShortComplex

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable (S : ShortComplex C) (F : C ⥤ D) [F.Additive]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The native homology comparison respects the original cycle projection. -/
theorem homologyπ_mapHomologyIso_hom :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  let h := S.leftHomologyData
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  dsimp only [Iso.trans, Functor.mapIso, Iso.symm, LeftHomologyData.map]
  simp only [← Category.assoc, LeftHomologyData.homologyπ_comp_homologyIso_hom]
  rw [Category.assoc, ← F.map_comp, LeftHomologyData.π_comp_homologyIso_inv,
    F.map_comp, Category.assoc]

/-- The native opcycle comparison respects the original cokernel projection. -/
theorem pOpcycles_mapOpcyclesIso_hom :
    (S.map F).pOpcycles ≫ (S.mapOpcyclesIso F).hom = F.map S.pOpcycles := by
  let h := S.rightHomologyData
  rw [h.mapOpcyclesIso_eq F]
  dsimp only [Iso.trans, Functor.mapIso, Iso.symm, RightHomologyData.map]
  simp only [← Category.assoc, RightHomologyData.pOpcycles_comp_opcyclesIso_hom]
  rw [← F.map_comp, RightHomologyData.p_comp_opcyclesIso_inv]

/-- The native homology comparison respects the inclusion into opcycles. -/
theorem mapHomologyIso_hom_homologyι :
    (S.mapHomologyIso F).hom ≫ F.map S.homologyι =
      (S.map F).homologyι ≫ (S.mapOpcyclesIso F).hom := by
  let h := S.rightHomologyData
  rw [← S.mapHomologyIso'_eq_mapHomologyIso F, h.mapHomologyIso'_eq F,
    h.mapOpcyclesIso_eq F]
  dsimp only [Iso.trans, Functor.mapIso, Iso.symm, RightHomologyData.map]
  rw [Category.assoc, ← F.map_comp, h.homologyIso_inv_comp_homologyι, F.map_comp]
  have hh := (h.map F).homologyIso_hom_comp_ι
  dsimp only [RightHomologyData.map] at hh
  rw [← Category.assoc, hh, Category.assoc]

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable {ι : Type u₃} {c : ComplexShape ι}
variable (F : C ⥤ D) [F.Additive]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The original differential from opcycles to cycles commutes with the native comparisons. -/
theorem opcyclesToCycles_mapCyclesIso_hom (K : HomologicalComplex C c) (i j : ι) :
    ((F.mapHomologicalComplex c).obj K).opcyclesToCycles i j ≫
        ((K.sc j).mapCyclesIso F).hom =
      ((K.sc i).mapOpcyclesIso F).hom ≫ F.map (K.opcyclesToCycles i j) := by
  have hi : ((K.sc j).mapCyclesIso F).hom ≫ F.map (K.iCycles j) =
      ((F.mapHomologicalComplex c).obj K).iCycles j :=
    ShortComplex.mapCyclesIso_hom_iCycles (K.sc j) F
  have hp : ((F.mapHomologicalComplex c).obj K).pOpcycles i ≫
      ((K.sc i).mapOpcyclesIso F).hom = F.map (K.pOpcycles i) :=
    ShortComplex.pOpcycles_mapOpcyclesIso_hom (K.sc i) F
  apply (cancel_epi (((F.mapHomologicalComplex c).obj K).pOpcycles i)).1
  apply (cancel_mono (F.map (K.iCycles j))).1
  let L := (F.mapHomologicalComplex c).obj K
  calc
    (L.pOpcycles i ≫ L.opcyclesToCycles i j ≫ ((K.sc j).mapCyclesIso F).hom) ≫
        F.map (K.iCycles j) = L.pOpcycles i ≫ L.opcyclesToCycles i j ≫ L.iCycles j := by
      erw [Category.assoc, Category.assoc, hi]
    _ = L.d i j := pOpcycles_opcyclesToCycles_iCycles L i j
    _ = F.map (K.d i j) := rfl
    _ = F.map (K.pOpcycles i ≫ K.opcyclesToCycles i j ≫ K.iCycles j) :=
      congrArg F.map (pOpcycles_opcyclesToCycles_iCycles K i j).symm
    _ = F.map (K.pOpcycles i) ≫ F.map (K.opcyclesToCycles i j) ≫ F.map (K.iCycles j) := by
      rw [F.map_comp, F.map_comp]
    _ = (F.map (K.pOpcycles i) ≫ F.map (K.opcyclesToCycles i j)) ≫
        F.map (K.iCycles j) := (Category.assoc _ _ _).symm
    _ = ((L.pOpcycles i ≫ ((K.sc i).mapOpcyclesIso F).hom) ≫
        F.map (K.opcyclesToCycles i j)) ≫ F.map (K.iCycles j) :=
      congrArg (fun t => (t ≫ F.map (K.opcyclesToCycles i j)) ≫ F.map (K.iCycles j)) hp.symm
    _ = (L.pOpcycles i ≫ ((K.sc i).mapOpcyclesIso F).hom ≫
        F.map (K.opcyclesToCycles i j)) ≫ F.map (K.iCycles j) :=
      congrArg (fun t => t ≫ F.map (K.iCycles j)) (Category.assoc _ _ _)

namespace HomologySequence

variable {S : ShortComplex (HomologicalComplex C c)} (hS : S.ShortExact)
variable (i j : ι) (hij : c.Rel i j)

/-- The native cycle/opcycle/homology comparisons form a morphism of snake inputs. -/
def mapSnakeComparison :
    snakeInput (hS.map_of_exact (F.mapHomologicalComplex c)) i j hij ⟶
      (snakeInput hS i j hij).map F where
  f₀ :=
    { τ₁ := ((S.X₁.sc i).mapHomologyIso F).hom
      τ₂ := ((S.X₂.sc i).mapHomologyIso F).hom
      τ₃ := ((S.X₃.sc i).mapHomologyIso F).hom
      comm₁₂ := (ShortComplex.mapHomologyIso_hom_naturality
        ((shortComplexFunctor C c i).map S.f) F).symm
      comm₂₃ := (ShortComplex.mapHomologyIso_hom_naturality
        ((shortComplexFunctor C c i).map S.g) F).symm }
  f₁ :=
    { τ₁ := ((S.X₁.sc i).mapOpcyclesIso F).hom
      τ₂ := ((S.X₂.sc i).mapOpcyclesIso F).hom
      τ₃ := ((S.X₃.sc i).mapOpcyclesIso F).hom
      comm₁₂ := (ShortComplex.mapOpcyclesIso_hom_naturality
        ((shortComplexFunctor C c i).map S.f) F).symm
      comm₂₃ := (ShortComplex.mapOpcyclesIso_hom_naturality
        ((shortComplexFunctor C c i).map S.g) F).symm }
  f₂ :=
    { τ₁ := ((S.X₁.sc j).mapCyclesIso F).hom
      τ₂ := ((S.X₂.sc j).mapCyclesIso F).hom
      τ₃ := ((S.X₃.sc j).mapCyclesIso F).hom
      comm₁₂ := (ShortComplex.mapCyclesIso_hom_naturality
        ((shortComplexFunctor C c j).map S.f) F).symm
      comm₂₃ := (ShortComplex.mapCyclesIso_hom_naturality
        ((shortComplexFunctor C c j).map S.g) F).symm }
  f₃ :=
    { τ₁ := ((S.X₁.sc j).mapHomologyIso F).hom
      τ₂ := ((S.X₂.sc j).mapHomologyIso F).hom
      τ₃ := ((S.X₃.sc j).mapHomologyIso F).hom
      comm₁₂ := (ShortComplex.mapHomologyIso_hom_naturality
        ((shortComplexFunctor C c j).map S.f) F).symm
      comm₂₃ := (ShortComplex.mapHomologyIso_hom_naturality
        ((shortComplexFunctor C c j).map S.g) F).symm }
  comm₀₁ := by
    ext
    all_goals exact ShortComplex.mapHomologyIso_hom_homologyι _ F
  comm₁₂ := by
    ext
    all_goals exact (opcyclesToCycles_mapCyclesIso_hom F _ i j).symm
  comm₂₃ := by
    ext
    all_goals exact (ShortComplex.homologyπ_mapHomologyIso_hom _ F).symm

/-- Exact functors preserve the actual homology-sequence boundary under the native comparison. -/
@[stacks 0111 "Homology-sequence ingredient; exact-functor compatibility is proved here"]
theorem mapHomologyIso_hom_δ :
    (hS.map_of_exact (F.mapHomologicalComplex c)).δ i j hij ≫
        ((S.X₁.sc j).mapHomologyIso F).hom =
      ((S.X₃.sc i).mapHomologyIso F).hom ≫ F.map (hS.δ i j hij) := by
  have h := ShortComplex.SnakeInput.naturality_δ (mapSnakeComparison F hS i j hij)
  change _ ≫ _ = _ ≫ ((snakeInput hS i j hij).map F).δ at h
  rw [ShortComplex.SnakeInput.map_δ] at h
  exact h

end HomologySequence
end HomologicalComplex
