/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Limits

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/BaseProduct.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 117]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
Actual product functors over the integral terminal scheme. Their natural transformations retain
genuine pullback squares, open-immersion and flatness preservation; fixed quasi-compact legs give
endofunctors of the honest full category of qc schemes.
-/
@[expose] public section


noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local simp] pullback.map pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc
universe u

namespace AlgebraicGeometry.Scheme.Products

/-- The genuine fiber product with a fixed scheme over the integral terminal scheme. -/
@[colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBase.lean:48"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def baseProductFunctor {S : AlgebraicGeometry.Scheme.{u}} (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) :
    AlgebraicGeometry.Scheme.{u} ⥤ AlgebraicGeometry.Scheme.{u} where
  obj X := pullback (specULiftZIsTerminal.from X) p
  map {X Y} f := pullback.map _ _ _ _ f (𝟙 S) (𝟙 (Spec (.of (ULift.{u} ℤ))))
    (by simp) (by simp)
  map_id X := by apply pullback.hom_ext <;> simp
  map_comp f g := by apply pullback.hom_ext <;> simp

/-- Its actual first projection, natural for every scheme map. -/
@[colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBase.lean:57"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def baseProductProjection {S : AlgebraicGeometry.Scheme.{u}} (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) :
    baseProductFunctor p ⟶ 𝟭 _ where
  app X := pullback.fst _ _
  naturality {X Y} f := by simp [baseProductFunctor]

/-- A genuine map over the integral base induces a natural map of these original products. -/
@[colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBase.lean:63"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def baseProductTransformation {S T : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) (f : S ⟶ T)
      (hf : f ≫ q = p) :
    baseProductFunctor p ⟶ baseProductFunctor q where
  app X := pullback.map _ _ _ _ (𝟙 X) f (𝟙 (Spec (.of (ULift.{u} ℤ)))) (by simp) (by
    simpa using hf.symm)
  naturality {X Y} g := by
    apply pullback.hom_ext <;> simp [baseProductFunctor]

@[reassoc (attr := simp), colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBase.lean:70"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
lemma baseProductTransformation_projection
    {S T : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) (f : S ⟶ T)
      (hf : f ≫ q = p)
    (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductTransformation p q f hf).app X ≫ (baseProductProjection q).app X =
      (baseProductProjection p).app X := by
  dsimp only [baseProductFunctor]
  simp [baseProductTransformation, baseProductProjection]

/-- The displayed natural map is an actual base change of the original fixed-factor map. -/
@[colib_tag "COL-0532", colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBase.lean:96"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
lemma baseProductTransformation_isPullback {S T : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) (f : S ⟶ T)
      (hf : f ≫ q = p)
    (X : AlgebraicGeometry.Scheme.{u}) :
    IsPullback ((baseProductTransformation p q f hf).app X)
      (pullback.snd (specULiftZIsTerminal.from X) p) (pullback.snd
        (specULiftZIsTerminal.from X) q) f := by
  dsimp only [baseProductFunctor]
  apply IsPullback.of_right (h₁₂ := pullback.fst (specULiftZIsTerminal.from X) q) (h₂₂ := q)
  · simpa [baseProductTransformation,hf] using (IsPullback.of_hasPullback
    (specULiftZIsTerminal.from X) p)
  · simp [baseProductTransformation]
  · exact IsPullback.of_hasPullback (specULiftZIsTerminal.from X) q

@[colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBase.lean:106"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
instance instIsOpenImmersionBaseProductTransformation {S T : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) (f : S ⟶ T)
      (hf : f ≫ q = p)
    [IsOpenImmersion f] (X : AlgebraicGeometry.Scheme.{u}) :
    IsOpenImmersion ((baseProductTransformation p q f hf).app X) :=
  MorphismProperty.of_isPullback (baseProductTransformation_isPullback p q f hf X).flip
    inferInstance

@[colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBase.lean:113"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
instance instFlatBaseProductTransformation {S T : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) (f : S ⟶ T)
      (hf : f ≫ q = p)
    [Flat f] (X : AlgebraicGeometry.Scheme.{u}) :
    Flat ((baseProductTransformation p q f hf).app X) :=
  MorphismProperty.of_isPullback (baseProductTransformation_isPullback p q f hf X).flip
    inferInstance


end AlgebraicGeometry.Scheme.Products

end

