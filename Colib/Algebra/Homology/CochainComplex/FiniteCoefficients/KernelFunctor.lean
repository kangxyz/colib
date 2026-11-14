/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Kernel
public import Colib.Algebra.Homology.CochainComplex.MappingCone.NativeShiftMap
public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Map
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Exact functors and the original multiplication-kernel comparison -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex.finiteCoefficients
universe v u v' u'
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
variable [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive]
variable [PreservesFiniteLimits F]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The actual preserved multiplication kernel, followed by a specified coefficient iso. -/
def kernelFunctorIso (G : C) (H : D) (e : F.obj G ≅ H) (n : ℕ) :
    F.obj (kernel (n • 𝟙 G)) ≅ kernel (n • 𝟙 H) :=
  PreservesKernel.iso F (n • 𝟙 G) ≪≫
    kernel.mapIso _ (n • 𝟙 H) e e (by simp)

/-- The canonical preserved-kernel iso respects the original kernel inclusion. -/
@[reassoc]
lemma kernelFunctorIso_hom_ι (G : C) (H : D) (e : F.obj G ≅ H) (n : ℕ) :
    (kernelFunctorIso F G H e n).hom ≫ kernel.ι (n • 𝟙 H) =
      F.map (kernel.ι (n • 𝟙 G)) ≫ e.hom := by
  simp [kernelFunctorIso]

/-- The actual morphism of power-map kernel sequences induced by the functor and coefficient iso. -/
def kernelSequenceFunctorMap (G : C) (H : D) (e : F.obj G ≅ H) (n : ℕ) :
    (ShortComplex.kernelSequence (n • 𝟙 G)).map F ⟶
      ShortComplex.kernelSequence (n • 𝟙 H) where
  τ₁ := (kernelFunctorIso F G H e n).hom
  τ₂ := e.hom
  τ₃ := e.hom
  comm₁₂ := kernelFunctorIso_hom_ι F G H e n
  comm₂₃ := by simp

/-- Native single-complex naturality followed by the actual preserved-kernel square. -/
def kernelSingleSequenceFunctorMap (G : C) (H : D) (e : F.obj G ≅ H) (n : ℕ) :
    (kernelSingleSequence G n).map (F.mapHomologicalComplex (.up ℤ)) ⟶
      kernelSingleSequence H n :=
  (ShortComplex.kernelSequence (n • 𝟙 G)).mapNatTrans
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom ≫
    (HomologicalComplex.single D (.up ℤ) 0).mapShortComplex.map
      (kernelSequenceFunctorMap F G H e n)

/-- Original single and shift transports for the coefficient iso. -/
def shiftedSingleFunctorIso (G : C) (H : D) (e : F.obj G ≅ H) :
    (F.mapHomologicalComplex (.up ℤ)).obj
      (((HomologicalComplex.single C (.up ℤ) 0).obj G)⟦(-1 : ℤ)⟧) ≅
      (((HomologicalComplex.single D (.up ℤ) 0).obj H)⟦(-1 : ℤ)⟧) :=
  ((F.mapHomologicalComplex (.up ℤ)).commShiftIso (-1)).app _ ≪≫
    (CategoryTheory.shiftFunctor _ (-1 : ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app G ≪≫
        (HomologicalComplex.single D (.up ℤ) 0).mapIso e)

omit [PreservesFiniteLimits F] in
/-- Arrow equality transports the original functor/cone comparison, without changing it. -/
lemma mapIso_arrow_eq (K : CochainComplex C ℤ) (n : ℕ)
    (g : K ⟶ K) (h : g = n • 𝟙 K)
    (h' : (F.mapHomologicalComplex (.up ℤ)).map g =
      n • 𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj K)) :
    (F.mapHomologicalComplex (.up ℤ)).map
      (eqToIso (congrArg (fun f : K ⟶ K => mappingCone f) h)).hom ≫
      (mapIso F K n).hom =
    (mappingCone.mapHomologicalComplexIso g F).hom ≫
      (eqToIso (congrArg (fun f :
        (F.mapHomologicalComplex (.up ℤ)).obj K ⟶
        (F.mapHomologicalComplex (.up ℤ)).obj K => mappingCone f) h')).hom := by
  subst g
  rw [mapIso_eq F K n h']
  simp

/-- The original finite functor map is the canonical transported kernel-sequence cone map. -/
lemma kernelSingleConeFunctor_map (G : C) (H : D) (e : F.obj G ≅ H) (n : ℕ) :
    (F.mapHomologicalComplex (.up ℤ)).map (kernelSingleConeIso G n).hom ≫
      (mapIso F (((HomologicalComplex.single C (.up ℤ) 0).obj G)⟦(-1 : ℤ)⟧) n).hom ≫
      map n (shiftedSingleFunctorIso F G H e).hom =
    (mappingCone.mapShiftedConeIso F (kernelSingleSequence G n).g).hom ≫
      mappingCone.map
        (((F.mapHomologicalComplex (.up ℤ)).map (kernelSingleSequence G n).g)⟦(-1 : ℤ)⟧')
        ((kernelSingleSequence H n).g⟦(-1 : ℤ)⟧')
        ((kernelSingleSequenceFunctorMap F G H e n).τ₂⟦(-1 : ℤ)⟧')
        ((kernelSingleSequenceFunctorMap F G H e n).τ₃⟦(-1 : ℤ)⟧')
        (by simpa only [Functor.map_comp, ShortComplex.map_g, ShortComplex.map_X₂,
          ShortComplex.map_X₃] using (congrArg
          (fun f => (CategoryTheory.shiftFunctor _ (-1 : ℤ)).map f)
          (kernelSingleSequenceFunctorMap F G H e n).comm₂₃.symm)) ≫
      (kernelSingleConeIso H n).hom := by
  let K := (((HomologicalComplex.single C (.up ℤ) 0).obj G)⟦(-1 : ℤ)⟧)
  let R := F.mapHomologicalComplex (.up ℤ)
  have hR : R.map ((kernelSingleSequence G n).g⟦(-1 : ℤ)⟧') = n • 𝟙 (R.obj K) := by
    rw [kernelSingleSequence_g_shift]
    change R.map (n • 𝟙 K) = n • 𝟙 (R.obj K)
    rw [R.map_nsmul, R.map_id]
  rw [← Category.assoc]
  erw [mapIso_arrow_eq F K n _ (kernelSingleSequence_g_shift G n) hR]
  rw [mappingCone.mapShiftedConeIso_hom]
  simp only [Category.assoc]
  rw [← mappingCone.map_comp_assoc]
  erw [mappingCone.map_arrow_eq _ _ hR (kernelSingleSequence_g_shift H n)]
  rfl

/-- The original single-kernel transport under the exact coefficient comparison. -/
def kernelSingleFunctorIso (G : C) (H : D) (e : F.obj G ≅ H) (n : ℕ) :
    (F.mapHomologicalComplex (.up ℤ)).obj
      ((HomologicalComplex.single C (.up ℤ) 0).obj (kernel (n • 𝟙 G))) ≅
      (HomologicalComplex.single D (.up ℤ) 0).obj (kernel (n • 𝟙 H)) :=
  (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app _ ≪≫
    (HomologicalComplex.single D (.up ℤ) 0).mapIso (kernelFunctorIso F G H e n)

/-- The actual map from the kernel commutes with the original finite functor comparison. -/
lemma fromKernelSingle_map (G : C) (H : D) (e : F.obj G ≅ H) (n : ℕ) :
    (F.mapHomologicalComplex (.up ℤ)).map (fromKernelSingle G n) ≫
      (mapIso F (((HomologicalComplex.single C (.up ℤ) 0).obj G)⟦(-1 : ℤ)⟧) n).hom ≫
      map n (shiftedSingleFunctorIso F G H e).hom =
    (kernelSingleFunctorIso F G H e n).hom ≫ fromKernelSingle H n := by
  dsimp only [fromKernelSingle]
  rw [Functor.map_comp, Category.assoc, kernelSingleConeFunctor_map]
  rw [← Category.assoc, mappingCone.fromShortComplex_map]
  rw [← Category.assoc]
  erw [mappingCone.fromShortComplex_naturality (kernelSingleSequenceFunctorMap F G H e n)]
  rw [Category.assoc]
  rfl

omit [PreservesFiniteLimits F] in
/-- The inverse of the existing derived kernel iso is exactly the existing kernel chain map. -/
lemma kernelSingleFiniteIso_inv [HasDerivedCategory C] (G : C) (n : ℕ) [Epi (n • 𝟙 G)] :
    (kernelSingleFiniteIso G n).inv = DerivedCategory.Q.map (fromKernelSingle G n) := by
  simp [kernelSingleFiniteIso, fromKernelSingle, kernelSingleConeIso,
    mappingCone.shiftedConeIso, Functor.map_comp]

variable [PreservesFiniteColimits F] [HasDerivedCategory C] [HasDerivedCategory D]

/-- Exact functors preserve the original finite kernel iso, through the native finite cone map. -/
lemma kernelSingleFiniteIso_map (G : C) (H : D) (e : F.obj G ≅ H) (n : ℕ)
    [Epi (n • 𝟙 G)] [Epi (n • 𝟙 H)] :
    DerivedCategory.Q.map
        ((mapIso F (((HomologicalComplex.single C (.up ℤ) 0).obj G)⟦(-1 : ℤ)⟧) n).hom ≫
          map n (shiftedSingleFunctorIso F G H e).hom) ≫
      (kernelSingleFiniteIso H n).hom =
    (F.mapDerivedCategoryFactors.app
      (finiteCoefficients (((HomologicalComplex.single C (.up ℤ) 0).obj G)⟦(-1 : ℤ)⟧) n)).inv ≫
      F.mapDerivedCategory.map (kernelSingleFiniteIso G n).hom ≫
      (F.mapDerivedCategoryFactors.app
        ((HomologicalComplex.single C (.up ℤ) 0).obj (kernel (n • 𝟙 G)))).hom ≫
      DerivedCategory.Q.map (kernelSingleFunctorIso F G H e n).hom := by
  have := quasiIso_fromKernelSingle G n
  have := quasiIso_fromKernelSingle H n
  apply (cancel_epi (DerivedCategory.Q.map
    ((F.mapHomologicalComplex (.up ℤ)).map (fromKernelSingle G n)))).mp
  rw [← DerivedCategory.Q.map_comp_assoc, fromKernelSingle_map, DerivedCategory.Q.map_comp]
  have hH := kernelSingleFiniteIso_inv (G := H) n
  rw [← hH, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [F.mapDerivedCategoryFactors.inv.naturality_assoc]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc]
  rw [← kernelSingleFiniteIso_inv (G := G) n, Iso.inv_hom_id,
    F.mapDerivedCategory.map_id, Category.id_comp]
  simp

end CochainComplex.finiteCoefficients
