/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.RelativeLineBoundary.Cone
import all Colib.AlgebraicGeometry.MotivicHomotopy.Purity.RelativeLineBoundary.Cone

/-!
# The ambient comparison for the projective Laurent cone

The comparison comes from the actual right inclusion after taking the
Laurent coefficient functor and the original Laurent augmentation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sm(" K ")" => SmoothSite (Spec (CommRingCat.of K))
local notation "PST(" K ")" => LargePresheaves K
local notation "NST(" K ")" => LargeSheaves K
local notation "G(" K ")" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of K))
local notation "A(" K ")" => nisnevichSheafify K
local notation "L(" K ")" => parameterTensorFunctor G(K)
local notation "Qs(" K ")" => (DerivedCategory.Q : CochainComplex NST(K) ℤ ⥤ DerivedCategory NST(K))
local notation "S(" K ")" => singleTransferSheafMinus K

private theorem compose_augmented_square {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {K L X Y : C} {A B : D}
    (a : A ⟶ B) (b : B ⟶ F.obj L) (l : A ⟶ F.obj K)
    (f : K ⟶ L) (u : L ⟶ Y) (x : K ⟶ X) (g : X ⟶ Y)
    (h₁ : a ≫ b = l ≫ F.map f) (h₂ : f ≫ u = x ≫ g) :
    a ≫ b ≫ F.map u = (l ≫ F.map x) ≫ F.map g := by
  rw [← Category.assoc a, h₁, Category.assoc, ← F.map_comp, h₂, F.map_comp,
    Category.assoc]

/-- Use the same abelian structure for the comparison of the line cones. -/
local instance instAbelianRelativeLineConeComparison : Abelian (NST(k)) :=
  SheafWithTransfers.abelian k

variable [HasDerivedCategory.{w} PST(k)] [HasDerivedCategory.{w'} NST(k)]

omit [HasDerivedCategory PST(k)] in
private theorem liftedSingle_map_shortComplex_g (Y : ShortComplex NST(k)) :
    ((S(k)).map Y.g).hom =
      Qs(k).map (Y.map (CochainComplex.singleFunctor NST(k) 0)).g := by
  change (DerivedCategory.singleFunctor NST(k) 0).map Y.g = _
  simp only [ShortComplex.map_g]
  rfl

set_option Elab.async false in
set_option maxHeartbeats 2200000 in
-- The final conversion compares the actual derived maps of the two Laurent augmentations.
/-- The Laurent augmentation restricts to the actual ambient Laurent quotient. -/
theorem projectiveLaurentPairComparison_ambient
    {U X : Sm(k)} (j : U ⟶ X) [IsOpenImmersion (torusCylinder.map j).left] :
    let J := Arrow.mk j
    let F := projectiveTorusTensorToDerivedMinus k
    let Y₀ := F.obj (singleTransferRepresentable k (Cor.mk X))
    let Y₁ := F.obj ((projectivePairDerived k).obj J)
    let V₀ := (S(k)).obj ((smoothTransferRepresentable k).obj (torusCylinder.obj X))
    let V₁ := (S(k)).obj ((transferPairCokernelFunctor k).obj ((laurentPair k).obj J))
    let a : Y₀ ⟶ Y₁ := F.map (projectivePairAmbientMap k J)
    let d : Y₁ ⟶ V₁ := (projectiveLaurentPairComparison k j).hom
    let e : Y₀ ⟶ V₀ := (projectiveAmbientLaurentIso k X).hom
    let v : V₀ ⟶ V₁ := projectiveAmbientLaurentQuotient k j
    a ≫ d = e ≫ v := by
  intro J F Y₀ Y₁ V₀ V₁ a d e v
  apply ObjectProperty.hom_ext
  let f := ((L(k) ⋙ A(k)).mapHomologicalComplex (.up ℤ)).map (ambientCochainMap k J)
  let u := (laurentCochainComparison k J).hom ≫ laurentCochainAugmentation k J
  let l := (projectiveTorusRepresentableSingleModelIso k (Cor.mk X)).hom
  let x := (laurentCochainEndpointIso k X).hom
  let g := (cochainTransferPair k ((laurentPair k).obj J)).g
  let b := (projectivePairTermwiseModelIso k L(k) J).hom
  have hd : d.hom = b ≫ Qs(k).map u := projectiveLaurentPairComparison_hom_hom k j
  have he : e.hom = l ≫ Qs(k).map x := projectiveAmbientLaurentIso_hom_hom k X
  have ha : a.hom ≫ b = l ≫ Qs(k).map f :=
    projectivePairTermwiseModelIso_ambient k L(k) J
  have hu : f ≫ u = x ≫ g := ambientCochain_laurent_aug k J
  change a.hom ≫ d.hom = e.hom ≫ (projectiveAmbientLaurentQuotient k j).hom
  rw [hd, he]
  unfold projectiveAmbientLaurentQuotient
  rw [liftedSingle_map_shortComplex_g]
  exact compose_augmented_square Qs(k) a.hom b l f u x g ha hu

end AlgebraicGeometry.MotivicHomotopy
