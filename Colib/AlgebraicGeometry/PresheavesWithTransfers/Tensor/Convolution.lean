/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor
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
  (prodOpEquiv (D := Cor k) (Cor k)).functor ⋙
    ((P.obj ⋙ integerModuleFunctor).prod (Q.obj ⋙ integerModuleFunctor)) ⋙
      MonoidalCategory.tensor MZ(k)

/-- Correspondences to the image of a pair, retaining their integral coefficients. -/
def convolutionCorrespondenceModule (X : Cor k) : CC(k) ⥤ MZ(k) :=
  Functor.uncurry.obj F ⋙ preadditiveCoyoneda.obj (op X) ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u} ⋙ integerModuleFunctor

/-- The two coefficient groups are tensored with the actual signed correspondence group. -/
def convolutionDiagram (P Q : PST(k)) (X : Cor k) : (CC(k))ᵒᵖ ⥤ CC(k) ⥤ MZ(k) :=
  Functor.curry.obj
    (((convolutionCoefficientModule P Q).prod (convolutionCorrespondenceModule F X)) ⋙
      MonoidalCategory.tensor MZ(k))

instance (P Q : PST(k)) (X : Cor k) : HasCoend (convolutionDiagram F P Q X) := by
  let : HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{u + 1} :=
    AddCommGrpCat.hasColimitsOfSize.{u + 1, u + 1, u + 1}
  let : HasColimitsOfSize.{u + 1, u + 1} MZ(k) := inferInstance
  infer_instance

/-- The section module of the integral convolution coend. -/
def convolutionSections (P Q : PST(k)) (X : Cor k) : MZ(k) :=
  coend (convolutionDiagram F P Q X)

/-- The coend inclusion, typed using the three original modules. -/
def convolutionInclusion (P Q : PST(k)) (X Y Z : Cor k) :
    ModuleCat.of ℤ ((sections P Y ⊗[ℤ] sections Q Z) ⊗[ℤ]
      ULift.{u + 1} (X ⟶ (F.obj Y).obj Z)) ⟶ convolutionSections F P Q X :=
  coend.ι (convolutionDiagram F P Q X) (Y, Z)

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
        (a ≫ convolutionCorrespondenceMap F f g) := by
  let A := convolutionCoefficientModule P Q
  let B := convolutionCorrespondenceModule F X
  let f' : (Y, Z) ⟶ (Y', Z') := (f, g)
  let j := convolutionInclusion F P Q X Y Z
  let j' := convolutionInclusion F P Q X Y' Z'
  let C := ModuleCat.of ℤ ((sections P Y' ⊗[ℤ] sections Q Z') ⊗[ℤ]
      ULift.{u + 1} (X ⟶ (F.obj Y).obj Z))
  let x : C := (s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a
  let l : C ⟶ ModuleCat.of ℤ ((sections P Y ⊗[ℤ] sections Q Z) ⊗[ℤ]
      ULift.{u + 1} (X ⟶ (F.obj Y).obj Z)) := A.map f'.op ⊗ₘ 𝟙 (B.obj (Y, Z))
  let r : C ⟶ ModuleCat.of ℤ ((sections P Y' ⊗[ℤ] sections Q Z') ⊗[ℤ]
      ULift.{u + 1} (X ⟶ (F.obj Y').obj Z')) := 𝟙 (A.obj (op (Y', Z'))) ⊗ₘ B.map f'
  have h₀ := coend.condition (convolutionDiagram F P Q X) f'
  change (A.map f'.op ⊗ₘ B.map (𝟙 (Y, Z))) ≫ j =
    (A.map (𝟙 (op (Y', Z'))) ⊗ₘ B.map f') ≫ j' at h₀
  rw [B.map_id, A.map_id] at h₀
  have h₁ : l ≫ j = r ≫ j' := h₀
  have h₂ : j (l x) = j' (r x) :=
    ConcreteCategory.congr_hom h₁ x
  change j (((transfer P f s) ⊗ₜ[ℤ] (transfer Q g t)) ⊗ₜ[ℤ] ULift.up a) =
    j' ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up (a ≫ convolutionCorrespondenceMap F f g)) at h₂
  exact h₂

/-- Maps from the coend are determined by its actual pure generators. -/
theorem convolutionSections_hom_ext (P Q : PST(k)) (X : Cor k)
    {M : MZ(k)} {f g : convolutionSections F P Q X ⟶ M}
    (h : ∀ (Y Z : Cor k) (s : sections P Y) (t : sections Q Z)
      (a : X ⟶ (F.obj Y).obj Z),
      f (convolutionGenerator F P Q X Y Z s t a) =
        g (convolutionGenerator F P Q X Y Z s t a)) : f = g := by
  apply coend.hom_ext
  rintro ⟨Y, Z⟩
  let j := convolutionInclusion F P Q X Y Z
  change j ≫ f = j ≫ g
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  rintro st ⟨a⟩
  refine TensorProduct.inductionOn st (fun s t => h Y Z s t a) ?_
  intro s t hs ht
  let W := ModuleCat.of ℤ ((sections P Y ⊗[ℤ] sections Q Z) ⊗[ℤ]
    ULift.{u + 1} (X ⟶ (F.obj Y).obj Z))
  let a₁ : W := s ⊗ₜ[ℤ] ULift.up a
  let a₂ : W := t ⊗ₜ[ℤ] ULift.up a
  have hsum : (s + t) ⊗ₜ[ℤ] ULift.up a = (a₁ + a₂ : W) := TensorProduct.add_tmul _ _ _
  calc
    (j ≫ f).hom ((s + t) ⊗ₜ[ℤ] ULift.up a) = (j ≫ f).hom (a₁ + a₂) := congrArg _ hsum
    _ = (j ≫ f).hom a₁ + (j ≫ f).hom a₂ := (j ≫ f).hom.map_add a₁ a₂
    _ = (j ≫ g).hom a₁ + (j ≫ g).hom a₂ := congrArg₂ (· + ·) hs ht
    _ = (j ≫ g).hom (a₁ + a₂) := ((j ≫ g).hom.map_add a₁ a₂).symm
    _ = (j ≫ g).hom ((s + t) ⊗ₜ[ℤ] ULift.up a) := congrArg _ hsum.symm

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
def convolutionPresheaf (P Q : PST(k)) : PST(k) := by
  let U := forget₂ MZ(k) AddCommGrpCat.{u + 1}
  let L : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    { obj X := U.obj (convolutionSections F P Q X.unop)
      map α := U.map (convolutionTransfer F P Q α.unop)
      map_id X := by
        rw [← U.map_id]
        apply congrArg U.map
        apply convolutionSections_hom_ext
        intro Y Z s t a
        simp only [unop_id, convolutionTransfer_generator, Category.id_comp,
          ModuleCat.id_apply]
      map_comp α β := by
        rw [← U.map_comp]
        apply congrArg U.map
        apply convolutionSections_hom_ext
        intro Y Z s t a
        simp only [unop_comp, ModuleCat.comp_apply, convolutionTransfer_generator,
          Category.assoc] }
  refine ⟨L, ⟨?_⟩⟩
  intro X Y α β
  change U.map (convolutionTransfer F P Q (α + β).unop) =
    U.map (convolutionTransfer F P Q α.unop) + U.map (convolutionTransfer F P Q β.unop)
  rw [← U.map_add]
  apply congrArg U.map
  apply convolutionSections_hom_ext
  intro Z W s t a
  change convolutionTransfer F P Q (α + β).unop (convolutionGenerator F P Q X.unop Z W s t a) =
    convolutionTransfer F P Q α.unop (convolutionGenerator F P Q X.unop Z W s t a) +
      convolutionTransfer F P Q β.unop (convolutionGenerator F P Q X.unop Z W s t a)
  simp only [convolutionTransfer_generator]
  change convolutionGenerator F P Q Y.unop Z W s t ((α.unop + β.unop) ≫ a) = _
  rw [Preadditive.add_comp, convolutionGenerator_add]


/-- Transfer in the convolution presheaf precomposes the correspondence label. -/
theorem convolutionPresheaf_transfer_generator (P Q : PST(k)) {X X' : Cor k} (f : X' ⟶ X)
    (Y Z : Cor k) (s : sections P Y) (t : sections Q Z) (a : X ⟶ (F.obj Y).obj Z) :
    transfer (convolutionPresheaf F P Q) f (convolutionGenerator F P Q X Y Z s t a) =
      convolutionGenerator F P Q X' Y Z s t (f ≫ a) :=
  convolutionTransfer_generator F P Q f Y Z s t a

end AlgebraicGeometry.PresheafWithTransfers
