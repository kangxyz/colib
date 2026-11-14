/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.DerivedCategory.ProjectiveSingleCoordinate
public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.KernelBoundary

/-! # The original finite reduction in degree one is the original extension boundary -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open Stacks.Cohomology.Corepresented
universe w v u
namespace CochainComplex.finiteCoefficients
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [HasExt C]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The original shifted finite reduction, in degree one, is canonical cancellation then Ext. -/
lemma integral_kernelSingleFiniteIso_extClass_one
    (G : C) (n : ℕ) [Epi (n • 𝟙 G)] :
    (DerivedCategory.Q.map (integral
      (((HomologicalComplex.single C (.up ℤ) 0).obj G)⟦(-1 : ℤ)⟧) n) ≫
      (kernelSingleFiniteIso G n).hom)⟦(1 : ℤ)⟧' =
    (derivedSingleNegOneCancelIso G).hom ≫ (kernelSequenceShortExact G n).extClass.hom := by
  rw [integral_kernelSingleFiniteIso_extClass]
  simp only [Functor.map_comp, shift_shiftFunctorCompIsoId_hom_app]
  erw [(shiftFunctorCompIsoId (DerivedCategory C) (-1 : ℤ) 1
    (by decide)).hom.naturality]
  simp only [derivedSingleNegOneCancelIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, DerivedCategory.singleFunctorIsoCompQ]
  simp only [Category.assoc]
  erw [Category.id_comp]
  rfl

end CochainComplex.finiteCoefficients
