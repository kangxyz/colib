/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.BaseChange.Products
public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.ZeroComparison
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Native group parameters under arbitrary change of ground scheme

Both parameter schemes are the existing integral group schemes pulled back from
Spec Z. Iterated pullback gives their canonical comparison, retaining the
integral coordinate, the positive Laurent inclusion and the whole zero section.
The polynomial spectrum is used only to identify the already chosen zero point.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S T : Scheme.{u}} (r : T ⟶ S)
local notation "Z₀" => Spec (CommRingCat.of (ULift ℤ))
local notation "s₀" => specULiftZIsTerminal.from S
local notation "t₀" => specULiftZIsTerminal.from T

/-- The literal iterated pullback of a fixed integral parameter. -/
def integralParameterBaseChangeIso {G : Scheme.{u}} (p : G ⟶ Z₀) :
    pullback (pullback.snd p s₀) r ≅ pullback p t₀ :=
  pullbackLeftPullbackSndIso p s₀ r ≪≫
    pullback.congrHom rfl (specULiftZIsTerminal.hom_ext (r ≫ s₀) t₀)

@[reassoc (attr := simp)] theorem integralParameterBaseChangeIso_fst
    {G : Scheme.{u}} (p : G ⟶ Z₀) :
    (integralParameterBaseChangeIso r p).hom ≫ pullback.fst p t₀ =
      pullback.fst (pullback.snd p s₀) r ≫ pullback.fst p s₀ := by
  simp only [integralParameterBaseChangeIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom, asIso_hom, pullback.map, pullback.lift_fst,
    Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

@[reassoc (attr := simp)] theorem integralParameterBaseChangeIso_snd
    {G : Scheme.{u}} (p : G ⟶ Z₀) :
    (integralParameterBaseChangeIso r p).hom ≫ pullback.snd p t₀ =
      pullback.snd (pullback.snd p s₀) r := by
  simp only [integralParameterBaseChangeIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom, asIso_hom, pullback.map, pullback.lift_snd,
    Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

/-- Base change of the existing native additive parameter is the same native parameter. -/
def nativeAdditiveBaseChangeIso :
    (baseChange r).obj (additiveGroupObject S) ≅ additiveGroupObject T :=
  MorphismProperty.Over.isoMk
    (integralParameterBaseChangeIso r (additiveGroup ↘ Z₀))
    (integralParameterBaseChangeIso_snd r _)

/-- Base change of the existing native multiplicative parameter, without inverting
its coordinate. -/
def nativeMultiplicativeBaseChangeIso :
    (baseChange r).obj (multiplicativeGroupObject S) ≅ multiplicativeGroupObject T :=
  MorphismProperty.Over.isoMk
    (integralParameterBaseChangeIso r (multiplicativeGroupULift ↘ Z₀))
    (integralParameterBaseChangeIso_snd r _)

@[reassoc (attr := simp)] theorem nativeAdditiveBaseChangeIso_integral :
    (nativeAdditiveBaseChangeIso r).hom.left ≫ pullback.fst (additiveGroup ↘ Z₀) t₀ =
      pullback.fst (additiveGroupObject S).hom r ≫ pullback.fst (additiveGroup ↘ Z₀) s₀ :=
  integralParameterBaseChangeIso_fst r _

@[reassoc (attr := simp)] theorem nativeMultiplicativeBaseChangeIso_integral :
    (nativeMultiplicativeBaseChangeIso r).hom.left ≫
      pullback.fst (multiplicativeGroupULift ↘ Z₀) t₀ =
    pullback.fst (multiplicativeGroupObject S).hom r ≫
      pullback.fst (multiplicativeGroupULift ↘ Z₀) s₀ :=
  integralParameterBaseChangeIso_fst r _

/-- The fixed positive Laurent inclusion is preserved as an actual morphism. -/
@[reassoc] theorem nativeParameterBaseChangeIso_open :
    (baseChange r).map (multiplicativeGroupOpen S) ≫ (nativeAdditiveBaseChangeIso r).hom =
      (nativeMultiplicativeBaseChangeIso r).hom ≫ multiplicativeGroupOpen T := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp only [MorphismProperty.Comma.comp_left, Category.assoc,
      nativeAdditiveBaseChangeIso_integral,
      multiplicativeGroupOpen_left, multiplicativeGroupBaseChangeToAdditive_fst,
      nativeMultiplicativeBaseChangeIso_integral_assoc]
    exact (baseChange_map_fst_assoc r (multiplicativeGroupOpen S)
      (pullback.fst (additiveGroup ↘ Z₀) s₀)).trans
      (congrArg (fun m => pullback.fst (multiplicativeGroupObject S).hom r ≫ m)
        (multiplicativeGroupBaseChangeToAdditive_fst S))
  · exact (MorphismProperty.Over.w
      ((baseChange r).map (multiplicativeGroupOpen S) ≫ (nativeAdditiveBaseChangeIso r).hom)).trans
      (MorphismProperty.Over.w
        ((nativeMultiplicativeBaseChangeIso r).hom ≫ multiplicativeGroupOpen T)).symm

/-- The original integral zero is a whole-base section of the native additive parameter. -/
def nativeZeroPoint (S : Scheme.{u}) : base S ⟶ additiveGroupObject S :=
  homMk (additiveGroupBaseChangeZero S) (additiveGroupBaseChangeZero_snd S)

/-- Its original polynomial comparison is precisely the previously chosen zero point. -/
theorem nativeZeroPoint_spec (A : CommRingCat.{u}) :
    nativeZeroPoint (Spec A) = Contraction.polynomialAffinePoint A 0 ≫
      (Contraction.affineLinePolynomialIso A).inv := by
  apply MorphismProperty.Over.Hom.ext
  exact (polynomial_zero_nativePolynomialAffineLineIso_inv A).symm

/-- Arbitrary base change preserves the full native zero point, including the base map. -/
@[reassoc] theorem nativeParameterBaseChangeIso_zero :
    (baseChange r).map (nativeZeroPoint S) ≫ (nativeAdditiveBaseChangeIso r).hom =
      (baseChangeBaseIso r).hom ≫ nativeZeroPoint T := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp only [MorphismProperty.Comma.comp_left, Category.assoc,
      nativeAdditiveBaseChangeIso_integral, nativeZeroPoint, homMk_left, baseChangeBaseIso_hom_left]
    have h := congrArg (fun f => f ≫ integralAdditiveZero)
      (specULiftZIsTerminal.hom_ext
        (pullback.fst (𝟙 S) r ≫ s₀) (pullback.snd (𝟙 S) r ≫ t₀))
    calc
      _ = pullback.fst (𝟙 S) r ≫
          additiveGroupBaseChangeZero S ≫ pullback.fst (additiveGroup ↘ Z₀) s₀ :=
        baseChange_map_fst_assoc r (nativeZeroPoint S) _
      _ = pullback.fst (𝟙 S) r ≫ s₀ ≫ integralAdditiveZero :=
        congrArg (fun m => pullback.fst (𝟙 S) r ≫ m) (additiveGroupBaseChangeZero_fst S)
      _ = pullback.snd (𝟙 S) r ≫ t₀ ≫ integralAdditiveZero :=
        (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))
      _ = _ := (congrArg (fun m => pullback.snd (𝟙 S) r ≫ m)
        (additiveGroupBaseChangeZero_fst T)).symm
  · exact (MorphismProperty.Over.w
      ((baseChange r).map (nativeZeroPoint S) ≫ (nativeAdditiveBaseChangeIso r).hom)).trans
      (MorphismProperty.Over.w ((baseChangeBaseIso r).hom ≫ nativeZeroPoint T)).symm

/-- The actual base structural map is preserved by the literal base comparison. -/
@[reassoc] theorem baseChange_toBase (X : SmoothSite S) :
    (baseChange r).map (Contraction.toBase X) ≫ (baseChangeBaseIso r).hom =
      Contraction.toBase ((baseChange r).obj X) := by
  apply MorphismProperty.Over.Hom.ext
  let f := (baseChange r).map (Contraction.toBase X) ≫ (baseChangeBaseIso r).hom
  have h := MorphismProperty.Over.w f
  change f.left ≫ 𝟙 T = ((baseChange r).obj X).hom at h
  exact (Category.comp_id f.left).symm.trans h

end AlgebraicGeometry.Scheme.SmoothSite
