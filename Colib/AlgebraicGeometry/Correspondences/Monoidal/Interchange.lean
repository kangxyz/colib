/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Category
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.WholeIncidenceCycles

/-!
# Interchange on native finite correspondences

The actual prime comparison extends to all four signed input cycles by
the native additive extensionality on finite correspondences.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Cor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] [PerfectField k]
  {X Y Z U V W : Cor k}

local infixr:70 " ⊠ₘ " => exteriorProduct

omit [PerfectField k] in
private theorem eq_of_prime {X Y : Cor k} {A : Type u} [AddCommGroup A]
    (F G : (X ⟶ Y) →+ A) (a : X ⟶ Y)
    (h : ∀ z (hz : IsFiniteCorrespondencePoint X.toSmoothSite.hom Y.toSmoothSite.hom z),
      F (singleFiniteCorrespondence _ _ z hz 1) = G (singleFiniteCorrespondence _ _ z hz 1)) :
    F a = G a :=
  DFunLike.congr_fun
    (finiteCorrespondences.addHom_ext_one X.toSmoothSite.hom Y.toSmoothSite.hom F G h) a

omit [PerfectField k] in
/-- Tensoring arbitrary signed correspondences preserves the actual Serre Tor composition. -/
@[colib_tag "COL-1296", colib_ref "MVW2006" "Lecture 1, Definition 1.9, p. 6"
  "background" "Exterior-product convention; arbitrary-field interchange is proved here."]
theorem exteriorInterchange : ExteriorInterchange k := by
  intro X Y Z U V W a c b d
  let T := tensorObj X U
  let L₁ := (Preadditive.rightComp T (b ⊠ₘ d)).comp (exteriorProduct.flip c)
  let R₁ := (exteriorProduct.flip (c ≫ d)).comp (Preadditive.rightComp X b)
  apply eq_of_prime L₁ R₁ a
  intro z hz
  let a₀ : X ⟶ Y := singleFiniteCorrespondence _ _ z hz 1
  change (a₀ ⊠ₘ c) ≫ (b ⊠ₘ d) = (a₀ ≫ b) ⊠ₘ (c ≫ d)
  let L₂ := (Preadditive.rightComp T (b ⊠ₘ d)).comp (exteriorProduct a₀)
  let R₂ := (exteriorProduct (a₀ ≫ b)).comp (Preadditive.rightComp U d)
  apply eq_of_prime L₂ R₂ c
  intro w hw
  let c₀ : U ⟶ V := singleFiniteCorrespondence _ _ w hw 1
  change (a₀ ⊠ₘ c₀) ≫ (b ⊠ₘ d) = (a₀ ≫ b) ⊠ₘ (c₀ ≫ d)
  let L₃ := (Preadditive.leftComp (tensorObj Z W) (a₀ ⊠ₘ c₀)).comp (exteriorProduct.flip d)
  let R₃ := (exteriorProduct.flip (c₀ ≫ d)).comp (Preadditive.leftComp Z a₀)
  apply eq_of_prime L₃ R₃ b
  intro z' hz'
  let b₀ : Y ⟶ Z := singleFiniteCorrespondence _ _ z' hz' 1
  change (a₀ ⊠ₘ c₀) ≫ (b₀ ⊠ₘ d) = (a₀ ≫ b₀) ⊠ₘ (c₀ ≫ d)
  let L₄ := (Preadditive.leftComp (tensorObj Z W) (a₀ ⊠ₘ c₀)).comp (exteriorProduct b₀)
  let R₄ := (exteriorProduct (a₀ ≫ b₀)).comp (Preadditive.leftComp W c₀)
  apply eq_of_prime L₄ R₄ d
  intro w' hw'
  let d₀ : V ⟶ W := singleFiniteCorrespondence _ _ w' hw' 1
  change (a₀ ⊠ₘ c₀) ≫ (b₀ ⊠ₘ d₀) = (a₀ ≫ b₀) ⊠ₘ (c₀ ≫ d₀)
  change incidenceTorPairing (tensorObj X U).toSmoothSite.hom (tensorObj Y V).toSmoothSite.hom
      (tensorObj Z W).toSmoothSite.hom (a₀ ⊠ₘ c₀) (b₀ ⊠ₘ d₀) =
    (incidenceTorPairing X.toSmoothSite.hom Y.toSmoothSite.hom Z.toSmoothSite.hom a₀ b₀) ⊠ₘ
      (incidenceTorPairing U.toSmoothSite.hom V.toSmoothSite.hom W.toSmoothSite.hom c₀ d₀)
  change incidenceTorPairing (SmoothSite.product X.toSmoothSite U.toSmoothSite).hom
      (SmoothSite.product Y.toSmoothSite V.toSmoothSite).hom
      (SmoothSite.product Z.toSmoothSite W.toSmoothSite).hom
      (correspondenceExterior X.toSmoothSite Y.toSmoothSite U.toSmoothSite V.toSmoothSite a₀ c₀)
      (correspondenceExterior Y.toSmoothSite Z.toSmoothSite V.toSmoothSite W.toSmoothSite b₀ d₀) =
    correspondenceExterior X.toSmoothSite Z.toSmoothSite U.toSmoothSite W.toSmoothSite
      (incidenceTorPairing X.toSmoothSite.hom Y.toSmoothSite.hom Z.toSmoothSite.hom a₀ b₀)
      (incidenceTorPairing U.toSmoothSite.hom V.toSmoothSite.hom W.toSmoothSite.hom c₀ d₀)
  dsimp only [a₀, b₀, c₀, d₀]
  rw [correspondenceExterior_single X.toSmoothSite Y.toSmoothSite U.toSmoothSite V.toSmoothSite
      z w hz hw 1 1,
    correspondenceExterior_single Y.toSmoothSite Z.toSmoothSite V.toSmoothSite W.toSmoothSite
      z' w' hz' hw' 1 1]
  simp only [incidenceTorPairing_single, one_mul, one_smul]
  exact incidenceTorPairing_exteriorPrimes X.toSmoothSite Y.toSmoothSite Z.toSmoothSite
    U.toSmoothSite V.toSmoothSite W.toSmoothSite z z' w w' hz hz' hw hw'

end AlgebraicGeometry.Cor
