/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Tensor.ConvolutionLocalEquivalences
public import Mathlib.CategoryTheory.Localization.Adjunction
public import StacksFrontier.CategoryTheory.Localization.Monoidal

import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-!
# Symmetric convolution on actual Nisnevich sheaves with transfers

The monoidal local equivalences are proved from the canonical representable
presentations. Existing monoidal localization then supplies the coherence on
NST itself. No new category model or assumed tensor-stability premise is used.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]

/-- Fix the coefficient universe using the existing sheafification theorem. -/
local instance monoidalLocalizationCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

local notation "PST" => TransferCoefficients k
local notation "NST" => LargeSheaves k

/-- The morphisms inverted by the actual Nisnevich sheafification with transfers. -/
def nisnevichSheafificationEquivalences : MorphismProperty PST :=
  (MorphismProperty.isomorphisms NST).inverseImage (nisnevichSheafify k)

instance : (nisnevichSheafificationEquivalences k).IsMultiplicative :=
  inferInstanceAs ((MorphismProperty.isomorphisms NST).inverseImage
    (nisnevichSheafify k)).IsMultiplicative

instance : (nisnevichSheafify k).IsLocalization (nisnevichSheafificationEquivalences k) :=
  (nisnevichSheafificationAdjunction k).isLocalization

local instance : MonoidalCategory PST := convolutionMonoidalCategory
local instance : SymmetricCategory PST := convolutionSymmetricCategory

/-- Nisnevich local equivalences are stable under the actual convolution in both slots. -/
instance nisnevichSheafificationEquivalences_isMonoidal :
    (nisnevichSheafificationEquivalences k).IsMonoidal where
  toIsMultiplicative := inferInstance
  whiskerLeft P _ _ f hf := by
    change IsIso ((nisnevichSheafify k).map f) at hf
    let := hf
    change IsIso ((nisnevichSheafify k).map
      (((convolutionBifunctor (curriedTensor (Cor k))).obj P).map f))
    exact isIso_sheafify_convolution_map_right P f
  whiskerRight f hf Q := by
    change IsIso ((nisnevichSheafify k).map f) at hf
    let := hf
    change IsIso ((nisnevichSheafify k).map
      (((convolutionBifunctor (curriedTensor (Cor k))).map f).app Q))
    exact isIso_sheafify_convolution_map_left f Q

/-- The actual sheaf category has the symmetric convolution tensor obtained by
localizing integral transfer convolution; its unit is the sheafified represented unit. -/
@[instance_reducible]
def nisnevichConvolutionMonoidalCategory : MonoidalCategory NST :=
  Localization.monoidalCategory (nisnevichSheafify k)
    (nisnevichSheafificationEquivalences k) (Iso.refl _)

/-- Nisnevich sheafification is strong monoidal for the descended convolution. -/
def nisnevichConvolutionSheafificationCoreMonoidal :
    letI := nisnevichConvolutionMonoidalCategory k
    (nisnevichSheafify k).CoreMonoidal :=
  Localization.coreMonoidal (nisnevichSheafify k)
    (nisnevichSheafificationEquivalences k) (Iso.refl _)

/-- The original convolution symmetry descends to actual transfer sheaves. -/
@[instance_reducible]
def nisnevichConvolutionSymmetricCategory :
    letI := nisnevichConvolutionMonoidalCategory k
    SymmetricCategory NST :=
  Localization.symmetricCategory (nisnevichSheafify k)
    (nisnevichSheafificationEquivalences k) (Iso.refl _)

/-- The localized tensor is canonically the sheafification of the convolution
of the original transfer coefficients. The comparison uses the actual
sheafification counit and the localization tensorator. -/
def nisnevichConvolutionTensorIso (P Q : NST) :
    letI := nisnevichConvolutionMonoidalCategory k
    P ⊗ Q ≅ (nisnevichSheafify k).obj
      (convolutionPresheaf (curriedTensor (Cor k)) ((forget k).obj P) ((forget k).obj Q)) := by
  letI := nisnevichConvolutionMonoidalCategory k
  let a := nisnevichSheafificationAdjunction k
  exact tensorIso (asIso (a.counit.app P)).symm (asIso (a.counit.app Q)).symm ≪≫
    (nisnevichConvolutionSheafificationCoreMonoidal k).μIso ((forget k).obj P) ((forget k).obj Q)

end AlgebraicGeometry.SheafWithTransfers
