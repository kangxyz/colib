/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Basic
public import Colib.Algebra.Homology.CochainComplex.MappingCone.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The finite coefficients of a shifted single object with surjective multiplication
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CochainComplex.finiteCoefficients
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Kernel SES on single complexes; epimorphy is the substantive Kummer input. -/
def kernelSingleSequence (G : C) (n : ℕ) : ShortComplex (CochainComplex C ℤ) :=
  (ShortComplex.kernelSequence (n • 𝟙 G)).map
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0)

lemma kernelSingleSequence_shortExact (G : C) (n : ℕ) [Epi (n • 𝟙 G)] :
    (kernelSingleSequence G n).ShortExact := by
  apply ShortComplex.ShortExact.map_of_exact
  exact ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _)
    inferInstance (by change Epi (n • 𝟙 G); infer_instance)

/-- Multiplication is transported through the actual single and shift functors. -/
lemma kernelSingleSequence_g_shift (G : C) (n : ℕ) :
    (kernelSingleSequence G n).g⟦(-1 : ℤ)⟧' =
      n • 𝟙 (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj G)⟦(-1 : ℤ)⟧) := by
  change ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map (n • 𝟙 G))⟦(-1 : ℤ)⟧' = _
  simp only [Functor.map_nsmul]
  congr 1
  exact ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).congr_map
    ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map_id G)).trans
      ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).map_id _)

/-- D(Abelian C) comparison for the actual shifted multiplication cone.
The native rotation and signed shift are retained. -/
@[colib_tag "COL-1234",
  colib_ref "mathlib_stable_localization_pin"
    "Mathlib/Algebra/Homology/HomotopyCategory/ShortExact.lean:138-169"
    "ingredient"
    "Native SES cone quasi-isomorphism, applied to the actual multiplication kernel sequence",
  colib_ref "mathlib_stable_localization_pin"
    "Mathlib/Algebra/Homology/HomotopyCategory/Pretriangulated.lean:203-229"
    "ingredient" "Canonical double-cone rotation, followed by the original shift comparison"]
def kernelSingleFiniteIso (G : C) (n : ℕ) [Epi (n • 𝟙 G)]
    [HasDerivedCategory C] :
    DerivedCategory.Q.obj (finiteCoefficients
      (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj G)⟦(-1 : ℤ)⟧) n) ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (kernel (n • 𝟙 G))) :=
  by
    let K := ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj G)⟦(-1 : ℤ)⟧
    let e : mappingCone ((kernelSingleSequence G n).g⟦(-1 : ℤ)⟧') ≅
        finiteCoefficients K n :=
      eqToIso (congrArg (fun f : K ⟶ K => mappingCone f)
        (kernelSingleSequence_g_shift G n))
    exact DerivedCategory.Q.mapIso e.symm ≪≫
      mappingCone.shiftedConeIso (kernelSingleSequence_shortExact G n)

end CochainComplex.finiteCoefficients

namespace CochainComplex.finiteCoefficients
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]

lemma multiplication_comm {G H : C} (n : ℕ) (f : G ⟶ H) :
    (n • 𝟙 G) ≫ f = f ≫ (n • 𝟙 H) := by
  rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul]
  exact congrArg (n • ·) ((Category.id_comp f).trans (Category.comp_id f).symm)

/-- The actual induced map on multiplication kernels. -/
def kernelMap {G H : C} (n : ℕ) (f : G ⟶ H) :
    kernel (n • 𝟙 G) ⟶ kernel (n • 𝟙 H) :=
  kernel.map _ _ f f (by simp)

/-- The actual morphism of multiplication kernel sequences. -/
def kernelSequenceMap {G H : C} (n : ℕ) (f : G ⟶ H) :
    ShortComplex.kernelSequence (n • 𝟙 G) ⟶
      ShortComplex.kernelSequence (n • 𝟙 H) where
  τ₁ := kernelMap n f
  τ₂ := f
  τ₃ := f
  comm₁₂ := by
    exact kernel.lift_ι _ _ _
  comm₂₃ := (multiplication_comm n f).symm

/-- The induced morphism of single-complex kernel sequences. -/
def kernelSingleSequenceMap {G H : C} (n : ℕ) (f : G ⟶ H) :
    kernelSingleSequence G n ⟶ kernelSingleSequence H n :=
  (HomologicalComplex.single C (ComplexShape.up ℤ) 0).mapShortComplex.map
    (kernelSequenceMap n f)

end CochainComplex.finiteCoefficients

namespace CochainComplex.finiteCoefficients
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Transport mapped and shifted multiplication to the original finite coefficient cone. -/
def kernelSingleConeIso (G : C) (n : ℕ) :
    mappingCone ((kernelSingleSequence G n).g⟦(-1 : ℤ)⟧') ≅
      finiteCoefficients
        (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj G)⟦(-1 : ℤ)⟧) n :=
  eqToIso (congrArg
    (fun g : (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj G)⟦(-1 : ℤ)⟧) ⟶
      (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj G)⟦(-1 : ℤ)⟧) =>
        mappingCone g) (kernelSingleSequence_g_shift G n))

/-- The canonical chain map from the single kernel to the original shifted finite cone. -/
def fromKernelSingle (G : C) (n : ℕ) :
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (kernel (n • 𝟙 G)) ⟶
      finiteCoefficients
        (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj G)⟦(-1 : ℤ)⟧) n :=
  mappingCone.fromShortComplex (kernelSingleSequence G n) ≫ (kernelSingleConeIso G n).hom

lemma fromKernelSingle_naturality {G H : C} (n : ℕ) (f : G ⟶ H) :
    fromKernelSingle G n ≫
      map n (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map f)⟦(-1 : ℤ)⟧') =
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map (kernelMap n f) ≫
      fromKernelSingle H n := by
  let m := kernelSingleSequenceMap n f
  have he := mappingCone.map_arrow_eq
    (m.τ₂⟦(-1 : ℤ)⟧') (m.τ₃⟦(-1 : ℤ)⟧')
    (kernelSingleSequence_g_shift G n) (kernelSingleSequence_g_shift H n)
    (by simpa only [Functor.map_comp] using
      (congrArg (fun g => (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1)).map g)
        m.comm₂₃.symm)) (multiplication_comm n (m.τ₂⟦(-1 : ℤ)⟧'))
  dsimp only [fromKernelSingle]
  rw [Category.assoc]
  erw [← he]
  rw [← Category.assoc, mappingCone.fromShortComplex_naturality]
  exact Category.assoc _ _ _

end CochainComplex.finiteCoefficients

namespace CochainComplex.finiteCoefficients
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

lemma quasiIso_fromKernelSingle (G : C) (n : ℕ) [Epi (n • 𝟙 G)] :
    QuasiIso (fromKernelSingle G n) := by
  have := mappingCone.quasiIso_fromShortComplex (kernelSingleSequence_shortExact G n)
  dsimp only [fromKernelSingle]
  infer_instance

@[colib_tag "COL-1234",
  colib_ref "mathlib_stable_localization_pin"
    "Mathlib/Algebra/Homology/HomotopyCategory/Pretriangulated.lean:150-177"
    "ingredient"
    "Actual cone maps and their composition; kernel and shift transports proved in this leaf"]
lemma kernelSingleFiniteIso_naturality [HasDerivedCategory C]
    {G H : C} (n : ℕ) [Epi (n • 𝟙 G)] [Epi (n • 𝟙 H)] (f : G ⟶ H) :
    DerivedCategory.Q.map
      (map n (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map f)⟦(-1 : ℤ)⟧')) ≫
      (kernelSingleFiniteIso H n).hom =
    (kernelSingleFiniteIso G n).hom ≫ DerivedCategory.Q.map
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map (kernelMap n f)) := by
  have := quasiIso_fromKernelSingle G n
  have := quasiIso_fromKernelSingle H n
  have := mappingCone.quasiIso_fromShortComplex (kernelSingleSequence_shortExact G n)
  have := mappingCone.quasiIso_fromShortComplex (kernelSingleSequence_shortExact H n)
  apply (cancel_epi (DerivedCategory.Q.map (fromKernelSingle G n))).mp
  rw [← DerivedCategory.Q.map_comp_assoc, fromKernelSingle_naturality,
    DerivedCategory.Q.map_comp]
  simp [kernelSingleFiniteIso, fromKernelSingle, kernelSingleConeIso,
    mappingCone.shiftedConeIso]

end CochainComplex.finiteCoefficients
