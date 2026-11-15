/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.StableMonoidal
public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.LefschetzSymmetry
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.NativeLefschetz
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.NativeParameter
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.SignedExactness
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-!
# The original tensor on geometric motives

The symmetric effective tensor restricts to the thick geometric
subcategory, and its Lefschetz transition identifies with the transition
of the original stable geometric category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme
open SmoothSite.Contraction
open scoped MonoidalCategory

universe u w w' w''

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]

local instance geometricTensorCorSheafify :
    HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (Cor.nisnevichTopology k)

local instance geometricTensorSmoothSheafify :
    HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1}
    (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))

/-- The canonical abelian structure used to form the effective convolution. -/
local instance geometricTensorGenericAbelian : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

variable [HasDerivedCategory.{w} (LargePresheaves k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "E" => EffectiveMotivesMinus k
local notation "P" => isEffectiveGeometric k
local notation "D" => GeometricMotives k

variable (e : ∀ T : SmoothSite (Spec (CommRingCat.of k)),
  Cor.graphFunctor k ⋙ (curriedTensor (Cor k)).flip.obj (Cor.mk T) ≅
    SmoothSite.Contraction.parameterProduct T ⋙ Cor.graphFunctor k)

/-- The actual effective tensor preserves the thick geometric object property. -/
theorem effectiveGeometricIsMonoidal :
    letI := effectiveSignedConvolutionMonoidalCategory e
    (P).IsMonoidal := by
  let := effectiveSignedConvolutionMonoidalCategory e
  let := effectiveSignedConvolutionSymmetricCategory e
  let := effectiveSignedConvolutionCommShift₂Int e
  let (A : E) : (tensorLeft A).IsTriangulated :=
    effectiveSignedTensorLeft_isTriangulated e A
  exact isEffectiveGeometric_monoidal_of_smoothProduct k
    (effectiveSignedConvolutionUnitIso e).symm
    (fun X Y => (effectiveRepresentedTensorIso e X Y).symm)

/-- The self-braiding on the original geometric Lefschetz object is the identity. -/
theorem geometricEffectiveLefschetz_braiding :
    letI := effectiveSignedConvolutionMonoidalCategory e
    letI := effectiveSignedConvolutionSymmetricCategory e
    letI := effectiveGeometricIsMonoidal k e
    (β_ (geometricEffectiveLefschetzMotive k) (geometricEffectiveLefschetzMotive k)).hom =
      𝟙 _ := by
  let := effectiveSignedConvolutionMonoidalCategory e
  let := effectiveSignedConvolutionSymmetricCategory e
  let := effectiveGeometricIsMonoidal k e
  apply (effectiveGeometricMotivesInclusion k).map_injective
  exact effectiveLefschetz_braiding e

section Native

local notation "EffGm" => EffectiveGeometricMotives k
local notation "J₀" => geometricMotivesInclusion k
local notation "M₀" => geometricMotive k
set_option quotPrecheck false in
local notation "d₀" => Cor.graphFunctorCompTensorRightIso (k := k)

/-- The actual tensor of the original Lefschetz object is the original
cancellation transition, including its choice of cochain shift. -/
abbrev effectiveLefschetzTensorComparison :
    letI := effectiveSignedConvolutionMonoidalCategory d₀
    tensorRight (effectiveLefschetzMotive k) ≅
      effectiveReducedTorusTensorFunctor k ⋙ shiftFunctor E (1 : ℤ) :=
  effectiveLefschetzTensorIso k

/-- The signed convolution tensor on effective motives. -/
local instance geometricTensorEffectiveMonoidal : MonoidalCategory E :=
  effectiveSignedConvolutionMonoidalCategory d₀

/-- The symmetry of the signed convolution tensor on effective motives. -/
local instance geometricTensorEffectiveSymmetric : SymmetricCategory E :=
  effectiveSignedConvolutionSymmetricCategory d₀

local instance geometricTensorEffectiveProperty : (P).IsMonoidal :=
  effectiveGeometricIsMonoidal k d₀

set_option quotPrecheck false in
local notation "L" => geometricEffectiveLefschetzMotive k
set_option quotPrecheck false in
local notation "αL" => geometricTensorRightLefschetzIso k (effectiveLefschetzTensorComparison k)
set_option quotPrecheck false in
local notation "βL" => geometricEffectiveLefschetz_braiding k d₀

/-- The original bounded-above effective tensor, restricted to geometric objects. -/
instance effectiveGeometricMotivesMonoidal : MonoidalCategory EffGm :=
  inferInstanceAs (MonoidalCategory (P).FullSubcategory)

/-- The effective full subcategory inherits the original symmetry. -/
instance effectiveGeometricMotivesSymmetric : SymmetricCategory EffGm :=
  inferInstanceAs (SymmetricCategory (P).FullSubcategory)

/-- The symmetric tensor on the original category of geometric motives. -/
instance geometricMotivesMonoidal : MonoidalCategory D :=
  geometricMotivesMonoidalCategoryOfTate k (αL) (βL)

/-- The symmetry uses the actual signed tensor at every finite stage. -/
instance geometricMotivesSymmetric : SymmetricCategory D :=
  geometricMotivesSymmetricCategoryOfTate k (αL) (βL)

/-- The stable tensor remains additive for the original geometric morphisms. -/
instance geometricMotivesMonoidalPreadditive : MonoidalPreadditive D := by
  let := effectiveSignedConvolutionMonoidalPreadditive d₀
  exact geometricMotivesMonoidalPreadditiveOfTate k (αL) (βL)

/-- The original inclusion of effective geometric motives preserves the tensor and braiding. -/
instance geometricMotivesInclusionBraided : (J₀).Braided :=
  let q := (Functor.FullyFaithful.ofFullyFaithful (geometricLefschetzTensor k)).ofIso (αL).symm
  letI := q.full
  letI := q.faithful
  Stabilization.transportedInclusionBraided L (αL) (βL)

/-- The tensor unit is the original geometric motive of the base. -/
def geometricMotiveUnitIso : 𝟙_ D ≅ (M₀).obj (𝟙_ (Cor k)) :=
  Functor.Monoidal.εIso J₀ ≪≫
    (J₀).mapIso ((P).isoMk (effectiveSignedConvolutionUnitIso d₀))

/-- Tensoring two original geometric motives gives the motive of the correspondence product. -/
def geometricMotiveTensorIso (X Y : Cor k) :
    (M₀).obj X ⊗ (M₀).obj Y ≅ (M₀).obj (X ⊗ Y) :=
  Functor.Monoidal.μIso J₀ ((effectiveGeometricMotive k).obj X) ((effectiveGeometricMotive k).obj Y)
    ≪≫ (J₀).mapIso ((P).isoMk (effectiveRepresentedTensorIso d₀ X Y))

/-- The product comparison commutes with the original geometric correspondence maps. -/
theorem geometricMotiveTensorIso_naturality {X X' Y Y' : Cor k}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    ((M₀).map f ⊗ₘ (M₀).map g) ≫ (geometricMotiveTensorIso k X' Y').hom =
      (geometricMotiveTensorIso k X Y).hom ≫ (M₀).map (f ⊗ₘ g) := by
  let I := J₀
  let B := effectiveGeometricMotive k
  let μ (U V : Cor k) : B.obj U ⊗ B.obj V ≅ B.obj (U ⊗ V) :=
    (P).isoMk (effectiveRepresentedTensorIso d₀ U V)
  have hμ : (B.map f ⊗ₘ B.map g) ≫ (μ X' Y').hom =
      (μ X Y).hom ≫ B.map (f ⊗ₘ g) :=
    (effectiveGeometricMotivesInclusion k).map_injective
      (effectiveRepresentedTensorIso_naturality d₀ f g)
  change (I.map (B.map f) ⊗ₘ I.map (B.map g)) ≫
      (Functor.LaxMonoidal.μ I (B.obj X') (B.obj Y') ≫ I.map (μ X' Y').hom) =
    (Functor.LaxMonoidal.μ I (B.obj X) (B.obj Y) ≫ I.map (μ X Y).hom) ≫
      I.map (B.map (f ⊗ₘ g))
  rw [Functor.LaxMonoidal.μ_natural_assoc, ← I.map_comp, hμ, I.map_comp, Category.assoc]

/-- The geometric product comparison carries the original correspondence braiding. -/
theorem geometricMotiveTensorIso_braiding (X Y : Cor k) :
    (β_ ((M₀).obj X) ((M₀).obj Y)).hom ≫ (geometricMotiveTensorIso k Y X).hom =
      (geometricMotiveTensorIso k X Y).hom ≫ (M₀).map (β_ X Y).hom := by
  let I := J₀
  let B := effectiveGeometricMotive k
  let μ (U V : Cor k) : B.obj U ⊗ B.obj V ≅ B.obj (U ⊗ V) :=
    (P).isoMk (effectiveRepresentedTensorIso d₀ U V)
  let f := (β_ (B.obj X) (B.obj Y)).hom
  let g := B.map (β_ X Y).hom
  have hμ : f ≫ (μ Y X).hom = (μ X Y).hom ≫ g :=
    (effectiveGeometricMotivesInclusion k).map_injective
      (effectiveRepresentedTensorIso_braiding d₀ X Y)
  change (β_ (I.obj (B.obj X)) (I.obj (B.obj Y))).hom ≫
    (Functor.LaxMonoidal.μ I (B.obj Y) (B.obj X) ≫ I.map (μ Y X).hom) =
    (Functor.LaxMonoidal.μ I (B.obj X) (B.obj Y) ≫ I.map (μ X Y).hom) ≫ I.map g
  rw [← Functor.LaxBraided.braided_assoc, ← I.map_comp, hμ, I.map_comp, Category.assoc]

end Native

end AlgebraicGeometry.MotivicHomotopy
