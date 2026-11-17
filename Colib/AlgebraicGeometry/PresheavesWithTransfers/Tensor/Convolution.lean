/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor
public import Colib.CategoryTheory.Preadditive.IntegralConvolutionPresheaf
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.Coefficients
public import Mathlib.CategoryTheory.Functor.Currying
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse

/-!
# The integral two-variable tensor coend

For a bifunctor on the actual finite-correspondence category, the coend
has generators consisting of two coefficient sections and a signed
correspondence to the image of their pair. Its relations are the two
transfer relations. The construction is additive in both coefficients
and in the original source correspondence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory TensorProduct

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- Integral coefficient modules in the universe of the native representables. -/
abbrev IntegerCoefficients (_ : Type u) := ModuleCat.{u + 1} ℤ

local notation "MZ(" K ")" => IntegerCoefficients K

local notation "PST(" K ")" => TransferCoefficients K

local notation "CC(" K ")" => Cor K × Cor K

variable (F : Cor k ⥤ Cor k ⥤ Cor k)

/-- The external tensor of the two original coefficient functors. -/
def convolutionCoefficientModule (P Q : PST(k)) : (CC(k))ᵒᵖ ⥤ MZ(k) :=
  CategoryTheory.Preadditive.Convolution.coefficientModule.{u + 1, u, 0} P.obj Q.obj

/-- Correspondences to the image of a pair, retaining their integral coefficients. -/
def convolutionCorrespondenceModule (X : Cor k) : CC(k) ⥤ MZ(k) :=
  CategoryTheory.Preadditive.Convolution.homModule.{u + 1, u, 0} F X

/-- The two coefficient groups are tensored with the actual signed correspondence group. -/
def convolutionDiagram (P Q : PST(k)) (X : Cor k) : (CC(k))ᵒᵖ ⥤ CC(k) ⥤ MZ(k) :=
  CategoryTheory.Preadditive.Convolution.diagram.{u + 1, u, 0} F P.obj Q.obj X

instance (P Q : PST(k)) (X : Cor k) : HasCoend (convolutionDiagram F P Q X) := by
  let : HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{u + 1} :=
    AddCommGrpCat.hasColimitsOfSize.{u + 1, u + 1, u + 1}
  let : HasColimitsOfSize.{u + 1, u + 1} MZ(k) := inferInstance
  infer_instance

/-- The section module of the integral convolution coend. -/
def convolutionSections (P Q : PST(k)) (X : Cor k) : MZ(k) :=
  CategoryTheory.Preadditive.Convolution.sections.{u + 1, u, 0} F P.obj Q.obj X

/-- The coend inclusion, typed using the three original modules. -/
def convolutionInclusion (P Q : PST(k)) (X Y Z : Cor k) :
    ModuleCat.of ℤ ((sections P Y ⊗[ℤ] sections Q Z) ⊗[ℤ]
      ULift.{u + 1} (X ⟶ (F.obj Y).obj Z)) ⟶ convolutionSections F P Q X :=
  CategoryTheory.Preadditive.Convolution.inclusion.{u + 1, u, 0} F P.obj Q.obj X Y Z

/-- A pair of sections and a signed correspondence give a pure coend generator. -/
def convolutionGenerator (P Q : PST(k)) (X Y Z : Cor k)
    (s : sections P Y) (t : sections Q Z) (a : X ⟶ (F.obj Y).obj Z) :
    convolutionSections F P Q X :=
  convolutionInclusion F P Q X Y Z ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a)

/-- The map of the correspondence bifunctor on a pair of arrows. -/
def convolutionCorrespondenceMap {Y Y' Z Z' : Cor k} (f : Y ⟶ Y') (g : Z ⟶ Z') :
    (F.obj Y).obj Z ⟶ (F.obj Y').obj Z' :=
  (F.map f).app Z ≫ (F.obj Y').map g

/-- The coend relation is the simultaneous transfer relation in the two factors. -/
theorem convolutionGenerator_transfer (P Q : PST(k)) {X Y Y' Z Z' : Cor k}
    (f : Y ⟶ Y') (g : Z ⟶ Z') (s : sections P Y') (t : sections Q Z')
    (a : X ⟶ (F.obj Y).obj Z) :
    convolutionGenerator F P Q X Y Z (transfer P f s) (transfer Q g t) a =
      convolutionGenerator F P Q X Y' Z' s t
        (a ≫ convolutionCorrespondenceMap F f g) :=
  CategoryTheory.Preadditive.Convolution.generator_transfer.{u + 1, u, 0} F P.obj Q.obj f g s t a

/-- Maps from the coend are determined by its actual pure generators. -/
theorem convolutionSections_hom_ext (P Q : PST(k)) (X : Cor k)
    {M : MZ(k)} {f g : convolutionSections F P Q X ⟶ M}
    (h : ∀ (Y Z : Cor k) (s : sections P Y) (t : sections Q Z)
      (a : X ⟶ (F.obj Y).obj Z),
      f (convolutionGenerator F P Q X Y Z s t a) =
        g (convolutionGenerator F P Q X Y Z s t a)) : f = g :=
  CategoryTheory.Preadditive.Convolution.sections_hom_ext.{u + 1, u, 0} F P.obj Q.obj X h

/-- Precompose the original correspondence component in the coend diagram. -/
def convolutionTransferDiagram (P Q : PST(k)) {X X' : Cor k} (β : X' ⟶ X) :
    convolutionDiagram F P Q X ⟶ convolutionDiagram F P Q X' :=
  Functor.curry.map (Functor.whiskerRight
    (NatTrans.prod (𝟙 (convolutionCoefficientModule P Q))
      (Functor.whiskerLeft (Functor.uncurry.obj F)
        (Functor.whiskerRight (preadditiveCoyoneda.map β.op)
          (AddCommGrpCat.uliftFunctor.{u + 1, u} ⋙ integerModuleFunctor))))
    (MonoidalCategory.tensor MZ(k)))

/-- Transfer of the convolution coend along the original correspondence. -/
def convolutionTransfer (P Q : PST(k)) {X X' : Cor k} (β : X' ⟶ X) :
    convolutionSections F P Q X ⟶ convolutionSections F P Q X' :=
  coend.map (convolutionTransferDiagram F P Q β)

@[simp]
theorem convolutionTransfer_generator (P Q : PST(k)) {X X' : Cor k} (β : X' ⟶ X)
    (Y Z : Cor k) (s : sections P Y) (t : sections Q Z) (a : X ⟶ (F.obj Y).obj Z) :
    convolutionTransfer F P Q β (convolutionGenerator F P Q X Y Z s t a) =
      convolutionGenerator F P Q X' Y Z s t (β ≫ a) :=
  ConcreteCategory.congr_hom (coend.ι_map (convolutionTransferDiagram F P Q β) (Y, Z))
    (show ((convolutionDiagram F P Q X).obj (op (Y, Z))).obj (Y, Z) from
      (s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a)

/-- Addition of source correspondences gives addition of pure generators. -/
theorem convolutionGenerator_add (P Q : PST(k)) {X Y Z : Cor k}
    (s : sections P Y) (t : sections Q Z) (a b : X ⟶ (F.obj Y).obj Z) :
    convolutionGenerator F P Q X Y Z s t (a + b) =
      convolutionGenerator F P Q X Y Z s t a +
        convolutionGenerator F P Q X Y Z s t b := by
  let j := convolutionInclusion F P Q X Y Z
  change j ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] (ULift.up a + ULift.up b)) =
    j ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a) + j ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up b)
  rw [TensorProduct.tmul_add, map_add]

/-- Addition in the first coefficient acts additively on generators. -/
theorem convolutionGenerator_add_left (P Q : PST(k)) {X Y Z : Cor k}
    (s s' : sections P Y) (t : sections Q Z) (a : X ⟶ (F.obj Y).obj Z) :
    convolutionGenerator F P Q X Y Z (s + s') t a =
      convolutionGenerator F P Q X Y Z s t a +
        convolutionGenerator F P Q X Y Z s' t a := by
  simp only [convolutionGenerator]
  rw [TensorProduct.add_tmul, TensorProduct.add_tmul, map_add]

/-- Addition in the second coefficient acts additively on generators. -/
theorem convolutionGenerator_add_right (P Q : PST(k)) {X Y Z : Cor k}
    (s : sections P Y) (t t' : sections Q Z) (a : X ⟶ (F.obj Y).obj Z) :
    convolutionGenerator F P Q X Y Z s (t + t') a =
      convolutionGenerator F P Q X Y Z s t a +
        convolutionGenerator F P Q X Y Z s t' a := by
  simp only [convolutionGenerator]
  rw [TensorProduct.tmul_add, TensorProduct.add_tmul, map_add]

/-- The integral tensor coend with its original additive transfer action. -/
def convolutionPresheaf (P Q : PST(k)) : PST(k) :=
  CategoryTheory.Preadditive.Convolution.presheaf.{u + 1, u, 0} F P.obj Q.obj

/-- Transfer in the convolution presheaf precomposes the correspondence label. -/
theorem convolutionPresheaf_transfer_generator (P Q : PST(k)) {X X' : Cor k} (f : X' ⟶ X)
    (Y Z : Cor k) (s : sections P Y) (t : sections Q Z) (a : X ⟶ (F.obj Y).obj Z) :
    transfer (convolutionPresheaf F P Q) f (convolutionGenerator F P Q X Y Z s t a) =
      convolutionGenerator F P Q X' Y Z s t (f ≫ a) :=
  convolutionTransfer_generator F P Q f Y Z s t a

end AlgebraicGeometry.PresheafWithTransfers
