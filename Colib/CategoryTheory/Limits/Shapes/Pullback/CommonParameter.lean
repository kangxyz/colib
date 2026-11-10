/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
public import Colib.Util.References

/-!
# Two products with one common parameter

The comparison is made entirely from native pullback associativity. Its three
coordinate equations retain the two original factors and the common parameter.
No geometric assumption enters this categorical identity.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u
namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {A B S T : C} (f : A ⟶ S) (g : B ⟶ S) (t : T ⟶ S)

/-- The product of two factors with one common parameter. -/
def pullbackCommonParameterIso :
    pullback (pullback.fst f g ≫ f) t ≅
      pullback (pullback.snd f t) (pullback.snd g t) :=
  pullback.congrHom pullback.condition rfl ≪≫
    pullbackAssoc f g g t ≪≫
    pullback.congrHom rfl (pullback.condition (f := g) (g := t)) ≪≫
    (pullbackLeftPullbackSndIso f t (pullback.snd g t)).symm

@[reassoc (attr := simp)]
theorem pullbackCommonParameterIso_hom_first :
    (pullbackCommonParameterIso f g t).hom ≫
      pullback.fst (pullback.snd f t) (pullback.snd g t) ≫ pullback.fst f t =
        pullback.fst _ t ≫ pullback.fst f g := by
  simp [pullbackCommonParameterIso, pullback.congrHom_hom, pullback.map, Category.assoc]

@[reassoc (attr := simp)]
theorem pullbackCommonParameterIso_hom_second :
    (pullbackCommonParameterIso f g t).hom ≫
      pullback.snd (pullback.snd f t) (pullback.snd g t) ≫ pullback.fst g t =
        pullback.fst _ t ≫ pullback.snd f g := by
  simp [pullbackCommonParameterIso, pullback.congrHom_hom, pullback.map, Category.assoc]

@[reassoc (attr := simp)]
theorem pullbackCommonParameterIso_hom_parameter :
    (pullbackCommonParameterIso f g t).hom ≫
      pullback.fst (pullback.snd f t) (pullback.snd g t) ≫ pullback.snd f t =
        pullback.snd _ t := by
  simp [pullbackCommonParameterIso, pullback.congrHom_hom, pullback.map, Category.assoc]

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/\
  CoefficientQuotient.lean:119-129,225-255"
  "generalization" "Native pullback reassociation and exact coordinates in any category \
  with pullbacks"]
  pullbackCommonParameterIso pullbackCommonParameterIso_hom_first
  pullbackCommonParameterIso_hom_second pullbackCommonParameterIso_hom_parameter

end CategoryTheory.Limits
