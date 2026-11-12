/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Steinberg.Equivalence
public import Colib.RingTheory.KTheory.Quillen.Field.SteinbergFiberInjectivity
public import Colib.RingTheory.KTheory.MilnorK.QuillenSurjectivity
public import Colib.RingTheory.KTheory.MilnorK.QuillenNaturality
public import Colib.RingTheory.KTheory.Quillen.Field.PositiveSymbolMarking

/-!
# Matsumoto's theorem for Quillen K₂

The forward maps are the original right-projective and upper finite-module maps.
Native Matsumoto injectivity, genuine stable-fiber perfectness and the constructed
geometric detector supply bijectivity. Both directions retain the original scalar
extension maps. The negative normalization is minus the same positive inverse.

The mathematical attribution is Matsumoto (1969), Section 5, Theorem 5.10 and
Corollary 5.11, pp. 30–31, specialized to stable type A over infinite fields.
Finite-field Milnor K₂ vanishing covers the finite fields. Weibel, III,
Theorem 6.1 gives the field K₂ formulation. The identification with
homotopy-defined K₂ is described in Weibel, IV, Corollary 1.7.1.

Implementation source: `Quillen/KTheory/Field/MilnorKTwoEquivalence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, generalized to all fields.
The ordered positive symbol is the original scalar identity-action unit
product. The negative normalization sends it to the negative ordered Milnor symbol.
-/
@[expose] public section

noncomputable section

universe u

namespace MilnorKTheory

open ModuleCat.FiniteProjective.StableCompletion
open CategoryTheory CategoryTheory.ExactCategory
attribute [local instance] StableSteinberg.kernelCommGroup Abelian.hasFiniteBiproducts

variable (F : Type u) [Field F]

/-- Injectivity of the original kernel map and the original kernel-to-K2 map
imply injectivity of their original right-projective composite. -/
theorem toRightProjectiveKTwo_injective :
    Function.Injective (toRightProjectiveKTwo F) := by
  intro x y h
  apply StableSteinberg.milnorToKernel_injective F
  apply Additive.toMul.injective
  apply steinbergKernelToRightProjectiveKTwo_injective F
  exact congrArg Additive.toMul h

/-- The original upper finite-module composite is injective. -/
theorem toUpperModuleKTwo_injective :
    Function.Injective (toUpperModuleKTwo F) := by
  intro x y h
  apply toRightProjectiveKTwo_injective F
  apply Additive.toMul.injective
  apply (FGModuleCat.rightProjectiveUpperModuleKEquiv F 2).injective
  exact congrArg Additive.toMul h

/-- The original right-projective map is bijective without any fiber-perfectness
or generation premise: the existing theorems supply both. -/
theorem toRightProjectiveKTwo_bijective :
    Function.Bijective (toRightProjectiveKTwo F) := by
  exact ⟨toRightProjectiveKTwo_injective F,
    toRightProjectiveKTwo_surjective F⟩

/-- The original upper finite-module map is bijective. -/
theorem toUpperModuleKTwo_bijective :
    Function.Bijective (toUpperModuleKTwo F) := by
  exact ⟨toUpperModuleKTwo_injective F,
    toUpperModuleKTwo_surjective F⟩

/-- Matsumoto's theorem with the original right-projective Quillen K₂ map. -/
def rightProjectiveKTwoEquiv : MilnorKTheory F 2 ≃+
    Additive ((ModuleCat.FiniteProjective.exactStructure.{u, u} Fᵐᵒᵖ).K 2) :=
  AddEquiv.ofBijective (toRightProjectiveKTwo F)
    (toRightProjectiveKTwo_bijective F)

/-- Matsumoto's theorem with the original upper finite-module Quillen K₂ map. -/
def upperModuleKTwoEquiv : MilnorKTheory F 2 ≃+
    Additive ((abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 2) :=
  AddEquiv.ofBijective (toUpperModuleKTwo F)
    (toUpperModuleKTwo_bijective F)

/-- The right-projective equivalence retains the literal original homomorphism. -/
theorem rightProjectiveKTwoEquiv_toAddMonoidHom :
    (rightProjectiveKTwoEquiv F).toAddMonoidHom =
      toRightProjectiveKTwo F := rfl

/-- The upper-model equivalence retains the literal original homomorphism. -/
theorem upperModuleKTwoEquiv_toAddMonoidHom :
    (upperModuleKTwoEquiv F).toAddMonoidHom =
      toUpperModuleKTwo F := rfl

/-- Applying the positive right-projective equivalence uses the original map. -/
@[simp] theorem rightProjectiveKTwoEquiv_apply (m : MilnorKTheory F 2) :
    rightProjectiveKTwoEquiv F m = toRightProjectiveKTwo F m := rfl

/-- Applying the positive upper-model equivalence uses the original map. -/
@[simp] theorem upperModuleKTwoEquiv_apply (m : MilnorKTheory F 2) :
    upperModuleKTwoEquiv F m = toUpperModuleKTwo F m := rfl

/-- The ordered right-projective symbol retains the original ordered kernel defect. -/
theorem rightProjectiveKTwoEquiv_pair (a b : Fˣ) :
    rightProjectiveKTwoEquiv F (milnorKTupleSymbol ![a, b]) = Additive.ofMul
      (steinbergKernelToRightProjectiveKTwo F (StableSteinberg.torusDefectKernel a b)) :=
  toRightProjectiveKTwo_pair F a b

/-- The ordered upper-model symbol is the original positive scalar unit product. -/
theorem upperModuleKTwoEquiv_pair (a b : Fˣ) :
    upperModuleKTwoEquiv F (milnorKTupleSymbol ![a, b]) =
      Additive.ofMul (FGModuleCat.FieldSymbols.unitProduct F a b) :=
  toUpperModuleKTwo_pair_eq_unitProduct F a b

variable {F} {L : Type u} [Field L] (f : F →+* L)

/-- The positive right-projective equivalence commutes with original scalar extension. -/
theorem rightProjectiveKTwoEquiv_naturality (m : MilnorKTheory F 2) :
    ((ModuleCat.FiniteProjective.rightBaseChangeExact f).KMap 2).toAdditive
        (rightProjectiveKTwoEquiv F m) =
      rightProjectiveKTwoEquiv L ((milnorKTheoryMap f 2).toAddMonoidHom m) :=
  toRightProjectiveKTwo_naturality f m

/-- The positive upper-model equivalence commutes with literal tensor extension. -/
theorem upperModuleKTwoEquiv_naturality (m : MilnorKTheory F 2) :
    ((FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive
        (upperModuleKTwoEquiv F m) =
      upperModuleKTwoEquiv L ((milnorKTheoryMap f 2).toAddMonoidHom m) :=
  toUpperModuleKTwo_naturality f m

/-- The inverse right-projective equivalence is natural for the original K-map. -/
theorem rightProjectiveKTwoEquiv_symm_naturality
    (z : Additive ((ModuleCat.FiniteProjective.exactStructure.{u, u} Fᵐᵒᵖ).K 2)) :
    (rightProjectiveKTwoEquiv L).symm
        (((ModuleCat.FiniteProjective.rightBaseChangeExact f).KMap 2).toAdditive z) =
      (milnorKTheoryMap f 2).toAddMonoidHom ((rightProjectiveKTwoEquiv F).symm z) := by
  have h := rightProjectiveKTwoEquiv_naturality f
    ((rightProjectiveKTwoEquiv F).symm z)
  rw [(rightProjectiveKTwoEquiv F).apply_symm_apply] at h
  exact (congrArg (rightProjectiveKTwoEquiv L).symm h).trans
    ((rightProjectiveKTwoEquiv L).symm_apply_apply _)

/-- The inverse upper-model equivalence is natural for original tensor extension. -/
theorem upperModuleKTwoEquiv_symm_naturality
    (z : Additive ((abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 2)) :
    (upperModuleKTwoEquiv L).symm
        (((FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive z) =
      (milnorKTheoryMap f 2).toAddMonoidHom ((upperModuleKTwoEquiv F).symm z) := by
  have h := upperModuleKTwoEquiv_naturality f
    ((upperModuleKTwoEquiv F).symm z)
  rw [(upperModuleKTwoEquiv F).apply_symm_apply] at h
  exact (congrArg (upperModuleKTwoEquiv L).symm h).trans
    ((upperModuleKTwoEquiv L).symm_apply_apply _)

variable (F)

/-- The explicitly NEGATIVE inverse of the positive upper-model equivalence. -/
def upperModuleKTwoNegativeEquiv :
    Additive ((abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 2) ≃+
      MilnorKTheory F 2 :=
  (upperModuleKTwoEquiv F).symm.trans (AddEquiv.neg _)

/-- The negative normalization is literally minus the positive inverse. -/
@[simp] theorem upperModuleKTwoNegativeEquiv_apply
    (z : Additive ((abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 2)) :
    upperModuleKTwoNegativeEquiv F z =
      -((upperModuleKTwoEquiv F).symm z) := rfl

/-- Normalizing the original forward Milnor map gives the negative input. -/
theorem upperModuleKTwoNegativeEquiv_milnor (m : MilnorKTheory F 2) :
    upperModuleKTwoNegativeEquiv F (toUpperModuleKTwo F m) = -m := by
  change -((upperModuleKTwoEquiv F).symm
    (upperModuleKTwoEquiv F m)) = -m
  rw [(upperModuleKTwoEquiv F).symm_apply_apply]

/-- The original forward map of a negatively normalized class is the negative class. -/
theorem toUpperModuleKTwo_negativeEquiv
    (z : Additive ((abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 2)) :
    toUpperModuleKTwo F (upperModuleKTwoNegativeEquiv F z) = -z := by
  change upperModuleKTwoEquiv F
    (-((upperModuleKTwoEquiv F).symm z)) = -z
  rw [map_neg, (upperModuleKTwoEquiv F).apply_symm_apply]

/-- The inverse negative normalization is minus the SAME original forward map. -/
theorem upperModuleKTwoNegativeEquiv_symm_apply (m : MilnorKTheory F 2) :
    (upperModuleKTwoNegativeEquiv F).symm m =
      -(toUpperModuleKTwo F m) := by
  apply (upperModuleKTwoNegativeEquiv F).injective
  rw [(upperModuleKTwoNegativeEquiv F).apply_symm_apply, map_neg,
    upperModuleKTwoNegativeEquiv_milnor, neg_neg]

/-- The actual positive ordered product normalizes to the negative ordered symbol. -/
theorem upperModuleKTwoNegativeEquiv_unitProduct (a b : Fˣ) :
    upperModuleKTwoNegativeEquiv F
        (Additive.ofMul (FGModuleCat.FieldSymbols.unitProduct F a b)) =
      -milnorKTupleSymbol ![a, b] := by
  rw [← toUpperModuleKTwo_pair_eq_unitProduct F a b,
    upperModuleKTwoNegativeEquiv_milnor]

variable {F}

/-- The negative normalization commutes with the original upper-model field map. -/
theorem upperModuleKTwoNegativeEquiv_naturality
    (z : Additive ((abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 2)) :
    upperModuleKTwoNegativeEquiv L
        (((FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive z) =
      (milnorKTheoryMap f 2).toAddMonoidHom (upperModuleKTwoNegativeEquiv F z) := by
  change -((upperModuleKTwoEquiv L).symm
    (((FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive z)) =
      (milnorKTheoryMap f 2).toAddMonoidHom (-((upperModuleKTwoEquiv F).symm z))
  rw [upperModuleKTwoEquiv_symm_naturality, map_neg]

/-- Homomorphism form of the negative normalization's original field-map square. -/
theorem upperModuleKTwoNegativeEquiv_naturality_hom :
    (upperModuleKTwoNegativeEquiv L).toAddMonoidHom.comp
        (((FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive) =
      ((milnorKTheoryMap f 2).toAddMonoidHom).comp
        (upperModuleKTwoNegativeEquiv F).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro z
  exact upperModuleKTwoNegativeEquiv_naturality f z

/-- The inverse negative normalization also commutes with the original field maps. -/
theorem upperModuleKTwoNegativeEquiv_symm_naturality (m : MilnorKTheory F 2) :
    ((FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u + 1} 2).toAdditive
        ((upperModuleKTwoNegativeEquiv F).symm m) =
      (upperModuleKTwoNegativeEquiv L).symm ((milnorKTheoryMap f 2).toAddMonoidHom m) := by
  rw [upperModuleKTwoNegativeEquiv_symm_apply,
    upperModuleKTwoNegativeEquiv_symm_apply, map_neg,
    toUpperModuleKTwo_naturality]

end MilnorKTheory

namespace MilnorKTheory

attribute [colib_ref "Matsumoto1969" "Section 5, Theorem 5.10 and Corollary 5.11, pp. 30-31"
    "adaptation" "Stable type A specialization over infinite fields, followed by \
      the separate identification with Quillen $K_2$",
  colib_ref "WeibelKBook" "III, Theorem 6.1" "adaptation"
    "Matsumoto's field $K_2$ presentation",
  colib_ref "WeibelKBook" "IV, Corollary 1.7.1" "comparison"
    "Identification of classical Steinberg-kernel $K_2$ with homotopy-defined $K_2$, realized here \
      in the existing exact-category models"]
  rightProjectiveKTwoEquiv upperModuleKTwoEquiv

attribute [colib_tag "COL-0262",
  colib_ref "quillen" "Quillen/KTheory/Field/MilnorKTwoEquivalence.lean, lines 73-226"
    "adaptation" "The characteristic-zero comparison and field-change formulas, \
      extended to all fields"]
  rightProjectiveKTwoEquiv upperModuleKTwoEquiv
  rightProjectiveKTwoEquiv_toAddMonoidHom upperModuleKTwoEquiv_toAddMonoidHom
  rightProjectiveKTwoEquiv_naturality upperModuleKTwoEquiv_naturality
  rightProjectiveKTwoEquiv_symm_naturality upperModuleKTwoEquiv_symm_naturality
  upperModuleKTwoEquiv_pair upperModuleKTwoNegativeEquiv
  upperModuleKTwoNegativeEquiv_apply upperModuleKTwoNegativeEquiv_unitProduct
  upperModuleKTwoNegativeEquiv_naturality
  upperModuleKTwoNegativeEquiv_symm_naturality

end MilnorKTheory
