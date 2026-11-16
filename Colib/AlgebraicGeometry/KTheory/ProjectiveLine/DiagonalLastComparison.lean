/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.DiagonalProjectedSequence
public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalQuotientAcyclic
public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalQuotientNaturality
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution

/-! # The diagonal coefficient under the first projection

The diagonal-supported quotient is acyclic for the first projection. The actual
Godement augmentation therefore becomes a quasi-isomorphism after taking ordinary
direct image. This identifies the terminal coefficient with the original input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen
open AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme.Modules.FlasquePerfect

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Q" => Limits.pullback π π
local notation "p₁" => Limits.pullback.fst π π
local notation "B" => BoundedBelowPerfect.projectiveLineDiagonalBoundedLast X
local notation "D₁" => (Functor.mapHomologicalComplex (pushforward p₁) (ComplexShape.up ℤ))

local instance : IsProper π := isProper_projectiveSpaceOver 1 X

/-- The pushforward of the literal augmentation on the diagonal-supported quotient is weak. -/
theorem projectiveLineDiagonalLastAugmentation_quasiIso (K : BoundedBelowPerfect.Obj P) :
    QuasiIso ((D₁).map (((unit Q).app ((B).obj K)).hom)) := by
  let L := (B).obj K
  let J := (total Q).obj L
  let f := ((unit Q).app L).hom
  let : QuasiIso f := unit_weak Q L
  apply (pushforward p₁).quasiIso_mapHomologicalComplex_of_rightAcyclic f
    L.property.2 J.property.1.2
  · intro j
    apply (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat (pushforward p₁) _).2
    exact fun n hn => projectiveLineDiagonalCoefficientLast_isZero_rightDerived X (K.obj.X j) n hn
  · intro j
    exact pushforward_rightAcyclic_of_flasque p₁ _ (J.property.2 j)

local notation "I" => BoundedBelowPerfect.inclusion P
local notation "i" => BoundedBelowPerfect.inclusion_exact P
local notation "W" => perfectComplexesWaldhausen
  (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace P))
local notation "e" => (IsExact.comp (BoundedBelowPerfect.projectiveLineDiagonalBoundedLast_exact X)
  (IsExact.comp (total_exact Q) (perfectPushforward_exact p₁)))

/-- The actual map on the original bounded-below complex, via the natural identification
of the ordinary last pushforward and the literal Godement augmentation. -/
def projectiveLineDiagonalLastComparison
    (α : (BoundedBelowPerfect.objects P).ι ≅
      B ⋙ (BoundedBelowPerfect.objects Q).ι ⋙ D₁) :
    I ⟶ projectiveLineDiagonalProjectedLast X where
  app K := ObjectProperty.homMk
    (α.hom.app K ≫ (D₁).map (((unit Q).app ((B).obj K)).hom))
  naturality {K L} g := by
    apply ObjectProperty.hom_ext
    let g' := (BoundedBelowPerfect.objects P).ι.map g
    let b := (B).map g
    let β := unit Q
    have hα : g' ≫ α.hom.app L =
        α.hom.app K ≫ (D₁).map b.hom := α.hom.naturality g
    have hβ : b.hom ≫ (β.app ((B).obj L)).hom =
        (β.app ((B).obj K)).hom ≫ ((total Q).map b).hom :=
      congrArg (fun k => k.hom) (β.naturality b)
    change g' ≫ (α.hom.app L ≫ (D₁).map (β.app ((B).obj L)).hom) =
      (α.hom.app K ≫ (D₁).map (β.app ((B).obj K)).hom) ≫ (D₁).map ((total Q).map b).hom
    rw [← Category.assoc, hα, Category.assoc, ← Functor.map_comp, hβ]
    exact (congrArg (fun m => α.hom.app K ≫ m)
      ((D₁).map_comp (β.app ((B).obj K)).hom ((total Q).map b).hom)).trans
      (Category.assoc _ _ _).symm

theorem projectiveLineDiagonalLastComparison_weak
    (α : (BoundedBelowPerfect.objects P).ι ≅
      B ⋙ (BoundedBelowPerfect.objects Q).ι ⋙ D₁) (K : BoundedBelowPerfect.Obj P) :
    (W).weq ((projectiveLineDiagonalLastComparison X α).app K) := by
  let : QuasiIso ((D₁).map (((unit Q).app ((B).obj K)).hom)) :=
    projectiveLineDiagonalLastAugmentation_quasiIso X K
  change QuasiIso (α.hom.app K ≫ (D₁).map (((unit Q).app ((B).obj K)).hom))
  infer_instance

/-- K-theoretic identification once the ordinary projection natural isomorphism is written. -/
theorem projectiveLineDiagonalLast_KMap_of_iso
    (α : (BoundedBelowPerfect.objects P).ι ≅
      B ⋙ (BoundedBelowPerfect.objects Q).ι ⋙ D₁) (n : ℕ) :
    KMap e n = KMap i n :=
  (KMap_eq_of_weakNatTrans i e (projectiveLineDiagonalLastComparison X α)
    (projectiveLineDiagonalLastComparison_weak X α) n).symm

/-- On actual bounded-below inputs, ordinary pushforward of the last coefficient is the identity. -/
def projectiveLineDiagonalLastCochainIso :
    (BoundedBelowPerfect.objects P).ι ≅ B ⋙ (BoundedBelowPerfect.objects Q).ι ⋙ D₁ := by
  let c := ComplexShape.up ℤ
  let j := (BoundedBelowPerfect.objects P).ι
  let A := (projectiveLineDiagonalSequence X).X₃
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor (Q).sheaf).obj A
  let L := Modules.pullback (Limits.pullback.snd π π)
  let R := Modules.pushforward p₁
  letI hT : T.PreservesZeroMorphisms :=
    Stacks.Sheaves.ChangeOfRings.preservesZeroMorphisms_sheafTensorObj (Q).sheaf A
  letI hL : L.PreservesZeroMorphisms := inferInstanceAs
    ((Modules.pullback (Limits.pullback.snd π π)).PreservesZeroMorphisms)
  letI hR : R.PreservesZeroMorphisms := inferInstanceAs
    ((Modules.pushforward p₁).PreservesZeroMorphisms)
  letI hLT : (L ⋙ T).PreservesZeroMorphisms := ⟨fun K J => by
    change T.map (L.map (0 : K ⟶ J)) = 0
    rw [L.map_zero]
    exact T.map_zero _ _⟩
  let α : (L ⋙ T) ⋙ R ≅ 𝟭 (P).Modules :=
    projectiveLineDiagonalCoefficientLastPushforwardNatIso X
  let γ := @Functor.mapHomologicalComplexCompIso _ _ _ _ _ _ _ _ _ _ L T (L ⋙ T)
    (Iso.refl (L ⋙ T)) hL hT hLT c
  let δ := @Functor.mapHomologicalComplexCompIso _ _ _ _ _ _ _ _ _ _ (L ⋙ T) R
    (𝟭 (P).Modules) α hLT hR inferInstance c ≪≫ Functor.mapHomologicalComplexIdIso _ c
  let ψ := Functor.isoWhiskerRight γ (D₁) ≪≫ δ
  exact (Functor.rightUnitor j).symm ≪≫ Functor.isoWhiskerLeft j ψ.symm

/-- The actual projected last term induces the identity on native K-groups. -/
theorem projectiveLineDiagonalLast_KMap (n : ℕ) : KMap e n = KMap i n :=
  projectiveLineDiagonalLast_KMap_of_iso X (projectiveLineDiagonalLastCochainIso X) n

end AlgebraicGeometry.Scheme.Modules.FlasquePerfect
