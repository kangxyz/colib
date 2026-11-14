/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.CochainComplex.MappingCone.ShortExactBoundary
public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Kernel

/-! # Finite coefficient reduction is the actual kernel extension boundary -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CochainComplex.finiteCoefficients

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

omit [HasDerivedCategory C] in
/-- The actual short exact multiplication kernel sequence. -/
lemma kernelSequenceShortExact (G : C) (n : ℕ) [Epi (n • 𝟙 G)] :
    (ShortComplex.kernelSequence (n • 𝟙 G)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _)
    inferInstance (by change Epi (n • 𝟙 G); infer_instance)

omit [HasDerivedCategory C] in
/-- Cone inclusion commutes with equality transport of its arrow. -/
lemma inr_arrow_eq {K L : CochainComplex C ℤ} {f g : K ⟶ L} (h : f = g) :
    mappingCone.inr f ≫ (eqToIso (congrArg (fun f : K ⟶ L => mappingCone f) h)).hom =
      mappingCone.inr g := by
  subst g
  simp

/-- Under the actual kernel comparison, integral reduction is the original Ext boundary.
The equality includes the original -1 shift and its actual cancellation isomorphism. -/
lemma integral_kernelSingleFiniteIso_extClass [HasExt C]
    (G : C) (n : ℕ) [Epi (n • 𝟙 G)] :
    DerivedCategory.Q.map (integral
      (((HomologicalComplex.single C (.up ℤ) 0).obj G)⟦(-1 : ℤ)⟧) n) ≫
      (kernelSingleFiniteIso G n).hom =
    (DerivedCategory.Q.commShiftIso (-1 : ℤ)).hom.app
      ((HomologicalComplex.single C (.up ℤ) 0).obj G) ≫
      ((kernelSequenceShortExact G n).extClass.hom)⟦(-1 : ℤ)⟧' ≫
      (shiftFunctorCompIsoId (DerivedCategory C) (1 : ℤ) (-1) (by simp)).hom.app
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single C (.up ℤ) 0).obj (kernel (n • 𝟙 G)))) := by
  let K := ((HomologicalComplex.single C (.up ℤ) 0).obj G)⟦(-1 : ℤ)⟧
  rw [ShortComplex.ShortExact.extClass_hom]
  dsimp only [kernelSingleFiniteIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← DerivedCategory.Q.map_comp_assoc]
  change DerivedCategory.Q.map
    (mappingCone.inr _ ≫ (eqToIso (congrArg (fun f : K ⟶ K => mappingCone f)
      (kernelSingleSequence_g_shift G n).symm)).hom) ≫ _ = _
  rw [inr_arrow_eq (kernelSingleSequence_g_shift G n).symm]
  exact mappingCone.inr_shiftedConeIso (kernelSingleSequence_shortExact G n)

end CochainComplex.finiteCoefficients
