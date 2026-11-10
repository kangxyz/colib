module

import Colib.CategoryTheory.Limits.Shapes.Pullback.CommonParameter

open CategoryTheory CategoryTheory.Limits

noncomputable section
universe v u

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {A B S T : C} (f : A ⟶ S) (g : B ⟶ S) (t : T ⟶ S)

example : pullback (pullback.fst f g ≫ f) t ≅
    pullback (pullback.snd f t) (pullback.snd g t) :=
  pullbackCommonParameterIso f g t

example : (pullbackCommonParameterIso f g t).hom ≫
    pullback.fst (pullback.snd f t) (pullback.snd g t) ≫ pullback.snd f t =
      pullback.snd _ t :=
  pullbackCommonParameterIso_hom_parameter f g t

example : (pullbackCommonParameterIso f g t).hom ≫
    pullback.fst (pullback.snd f t) (pullback.snd g t) ≫ pullback.fst f t =
      pullback.fst _ t ≫ pullback.fst f g :=
  pullbackCommonParameterIso_hom_first f g t

example : (pullbackCommonParameterIso f g t).hom ≫
    pullback.snd (pullback.snd f t) (pullback.snd g t) ≫ pullback.fst g t =
      pullback.fst _ t ≫ pullback.snd f g :=
  pullbackCommonParameterIso_hom_second f g t
