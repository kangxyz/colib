/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.CylinderExponential
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseFibrantDetection
import Colib.CategoryTheory.Sites.Simplicial.StalkwiseFibrantSmash
import Mathlib.CategoryTheory.Yoneda

/-!
# Locality tested by restriction to a point of the interval

For an injective fibrant target, the cylinder test in the actual
stalkwise localization is equivalent to the weak equivalence of its
exponential restriction to a specified point of the parameter.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  [MonoidalClosed (Cᵒᵖ ⥤ SSet.{w})]
  (J : GrothendieckTopology C)
  {I K : Cᵒᵖ ⥤ SSet.{w}} (s : I ⟶ K)
  {Y : PointedSimplicialPresheaf.{w} C} (hY : IsStalkwiseInjectiveFibrant C J Y)

set_option quotPrecheck false in
local notation "Q" => toStalkwiseHomotopyCategory C J

include hY in
/-- The constant-point exponential of a fibrant object is fibrant. -/
theorem isStalkwiseInjectiveFibrant_constantPointExponential
    (I : Cᵒᵖ ⥤ SSet.{w}) : IsStalkwiseInjectiveFibrant C J
      (Under.constantPointExponential I Y) :=
  isStalkwiseInjectiveFibrant_rightAdjoint_smash C J ((free C).obj I)
    (freeParameterSmashAdjunction I) hY

private def cylinderClassesToExponential (I : Cᵒᵖ ⥤ SSet.{w})
    (X : PointedSimplicialPresheaf.{w} C) :
    CylinderHomotopyClasses (parameterizedCylinder X I) Y ≃
      CylinderHomotopyClasses X (Under.constantPointExponential I Y) :=
  Equiv.ofBijective (cylinderHomotopyPrecomp (freeParameterSmashIso X I).hom)
    (bijective_cylinderHomotopyPrecomp_of_stalkwiseWeakEquivalence J hY
      (freeParameterSmashIso X I).hom
      (fun _ => SSet.IsRealizationWeakEquivalence.of_isIso _)) |>.trans
    (smashAdjunctionCylinderHomotopyEquiv ((free C).obj I)
      (freeParameterSmashAdjunction I) X Y)

private theorem cylinderClassesToExponential_mk (I : Cᵒᵖ ⥤ SSet.{w})
    (X : PointedSimplicialPresheaf.{w} C) (f : parameterizedCylinder X I ⟶ Y) :
    cylinderClassesToExponential J hY I X (_root_.Quotient.mk _ f) =
      _root_.Quotient.mk _ (cylinderExponentialHomEquiv I X Y f) := by
  change smashAdjunctionCylinderHomotopyEquiv ((free C).obj I)
    (freeParameterSmashAdjunction I) X Y
    (_root_.Quotient.mk _ ((freeParameterSmashIso X I).hom ≫ f)) = _
  rw [smashAdjunctionCylinderHomotopyEquiv_mk, freeParameterSmashAdjunction_homEquiv]
  rfl

private def cylinderExponentialStalkwiseHomEquiv (I : Cᵒᵖ ⥤ SSet.{w})
    (X : PointedSimplicialPresheaf.{w} C) :
    ((Q).obj (parameterizedCylinder X I) ⟶ (Q).obj Y) ≃
      ((Q).obj X ⟶ (Q).obj (Under.constantPointExponential I Y)) :=
  (stalkwiseFibrantHomEquiv J hY _).trans ((cylinderClassesToExponential J hY I X).trans
    (stalkwiseFibrantHomEquiv J (isStalkwiseInjectiveFibrant_constantPointExponential J hY I)
      X).symm)

private theorem cylinderExponentialStalkwiseHomEquiv_map (I : Cᵒᵖ ⥤ SSet.{w})
    (X : PointedSimplicialPresheaf.{w} C) (f : parameterizedCylinder X I ⟶ Y) :
    cylinderExponentialStalkwiseHomEquiv J hY I X ((Q).map f) =
      (Q).map (cylinderExponentialHomEquiv I X Y f) := by
  let h := isStalkwiseInjectiveFibrant_constantPointExponential J hY I
  let e := stalkwiseFibrantHomEquiv J h X
  let a := stalkwiseFibrantHomEquiv J hY (parameterizedCylinder X I)
  let b := cylinderClassesToExponential J hY I X
  change e.symm (b (a ((Q).map f))) = _
  apply e.injective
  rw [e.apply_symm_apply]
  exact (congrArg b (stalkwiseFibrantHomEquiv_map J hY _ f)).trans
    ((cylinderClassesToExponential_mk J hY I X f).trans
      (stalkwiseFibrantHomEquiv_map J h X _).symm)

private theorem cylinderExponentialStalkwiseHomEquiv_parameter
    (X : PointedSimplicialPresheaf.{w} C)
    (f : (Q).obj (parameterizedCylinder X K) ⟶ (Q).obj Y) :
    cylinderExponentialStalkwiseHomEquiv J hY I X
        ((Q).map (parameterizedCylinderParameterMap I s X) ≫ f) =
      cylinderExponentialStalkwiseHomEquiv J hY K X f ≫
        (Q).map (Under.constantPointExponentialPre s Y) := by
  obtain ⟨f₀, hf₀⟩ := surjective_stalkwise_map_of_isStalkwiseInjectiveFibrant J hY _ f
  change (Q).map f₀ = f at hf₀
  rw [← hf₀, ← (Q).map_comp, cylinderExponentialStalkwiseHomEquiv_map,
    cylinderExponentialStalkwiseHomEquiv_map, cylinderExponentialHomEquiv_parameter, (Q).map_comp]

include hY in
private theorem bijective_precomp_parameter_iff (X : PointedSimplicialPresheaf.{w} C) :
    Function.Bijective (fun f : (Q).obj (parameterizedCylinder X K) ⟶ (Q).obj Y ↦
      (Q).map (parameterizedCylinderParameterMap I s X) ≫ f) ↔
    Function.Bijective (fun f : (Q).obj X ⟶ (Q).obj (Under.constantPointExponential K Y) ↦
      f ≫ (Q).map (Under.constantPointExponentialPre s Y)) := by
  let e := cylinderExponentialStalkwiseHomEquiv J hY K X
  let e' := cylinderExponentialStalkwiseHomEquiv J hY I X
  let p := fun f : (Q).obj (parameterizedCylinder X K) ⟶ (Q).obj Y ↦
    (Q).map (parameterizedCylinderParameterMap I s X) ≫ f
  let q := fun f : (Q).obj X ⟶ (Q).obj (Under.constantPointExponential K Y) ↦
    f ≫ (Q).map (Under.constantPointExponentialPre s Y)
  have h : q = e' ∘ p ∘ e.symm := by
    funext f
    exact ((cylinderExponentialStalkwiseHomEquiv_parameter J s hY X (e.symm f)).trans
      (congrArg q (e.apply_symm_apply f))).symm
  change Function.Bijective p ↔ Function.Bijective q
  rw [h, Function.Bijective.of_comp_iff' e'.bijective,
    Function.Bijective.of_comp_iff _ e.symm.bijective]

include hY in
private theorem bijective_precomp_cylinderSection_iff
    (X : PointedSimplicialPresheaf.{w} C)
    (s : (⊤_ (Cᵒᵖ ⥤ SSet.{w})) ⟶ K) :
    Function.Bijective (fun f : (Q).obj (parameterizedCylinder X K) ⟶ (Q).obj Y ↦
      (Q).map (cylinderSection X s) ≫ f) ↔
    Function.Bijective (fun f : (Q).obj X ⟶ (Q).obj (Under.constantPointExponential K Y) ↦
      f ≫ (Q).map (Under.constantPointExponentialPre s Y)) := by
  let a : ((Q).obj X ⟶ (Q).obj Y) ≃
      ((Q).obj (parameterizedCylinder X (⊤_ _)) ⟶ (Q).obj Y) :=
    ((Q).mapIso (terminalParameterCylinderIso X)).symm.homFromEquiv
  have h := bijective_precomp_parameter_iff J s hY X
  rw [terminalParameterMap_section, (Q).map_comp] at h
  have he : (fun f : (Q).obj (parameterizedCylinder X K) ⟶ (Q).obj Y ↦
      ((Q).map (cylinderProjection X (⊤_ _)) ≫ (Q).map (cylinderSection X s)) ≫ f) =
      a ∘ (fun f : (Q).obj (parameterizedCylinder X K) ⟶ (Q).obj Y ↦
        (Q).map (cylinderSection X s) ≫ f) := by
    funext f
    exact Category.assoc _ _ _
  rw [he] at h
  change Function.Bijective (a ∘
    (fun f : (Q).obj (parameterizedCylinder X K) ⟶ (Q).obj Y ↦
      (Q).map (cylinderSection X s) ≫ f)) ↔ _ at h
  rw [Function.Bijective.of_comp_iff' a.bijective] at h
  exact h

include hY in
/-- For a fibrant presheaf, the original local tests are equivalent to
stalkwise weakness of restriction at the chosen parameter point. -/
theorem isIntervalLocal_iff_stalkwiseWeakEquivalences_exponentialPre
    (s : (⊤_ (Cᵒᵖ ⥤ SSet.{w})) ⟶ K) :
    IsIntervalLocal C J K ((Q).obj Y) ↔
      stalkwiseWeakEquivalences C J (Under.constantPointExponentialPre s Y) := by
  have hX (X : PointedSimplicialPresheaf.{w} C) :
      Function.Bijective (fun f : (Q).obj X ⟶ (Q).obj Y ↦
        (Q).map (cylinderProjection X K) ≫ f) ↔
      Function.Bijective (fun f : (Q).obj (parameterizedCylinder X K) ⟶ (Q).obj Y ↦
        (Q).map (cylinderSection X s) ≫ f) := by
    let p := fun f : (Q).obj X ⟶ (Q).obj Y ↦ (Q).map (cylinderProjection X K) ≫ f
    let a := fun f : (Q).obj (parameterizedCylinder X K) ⟶ (Q).obj Y ↦
      (Q).map (cylinderSection X s) ≫ f
    have ha : Function.LeftInverse a p := by
      intro f
      change (Q).map (cylinderSection X s) ≫ (Q).map (cylinderProjection X K) ≫ f = _
      rw [← (Q).map_comp_assoc, cylinderSection_projection, (Q).map_id, Category.id_comp]
    exact ⟨fun h => ⟨(ha.rightInverse_of_surjective h.surjective).injective, ha.surjective⟩,
      fun h => ⟨ha.injective, (ha.rightInverse_of_injective h.injective).surjective⟩⟩
  constructor
  · intro h
    apply stalkwiseWeakEquivalences_of_isIso_toStalkwiseHomotopyCategory_map
      (Under.constantPointExponentialPre s Y)
      (isStalkwiseInjectiveFibrant_constantPointExponential J hY K)
      (isStalkwiseInjectiveFibrant_constantPointExponential J hY (⊤_ _))
    apply isIso_of_yoneda_map_bijective
    intro Z
    let e := (Q).objObjPreimageIso Z
    let T := (Q).obj (Under.constantPointExponential K Y)
    let T' := (Q).obj (Under.constantPointExponential (⊤_ (Cᵒᵖ ⥤ SSet.{w})) Y)
    let p : T ⟶ T' := (Q).map (Under.constantPointExponentialPre s Y)
    let a : ((Q).obj ((Q).objPreimage Z) ⟶ T) ≃ (Z ⟶ T) := e.homFromEquiv
    let b : ((Q).obj ((Q).objPreimage Z) ⟶ T') ≃ (Z ⟶ T') := e.homFromEquiv
    have ht := (bijective_precomp_cylinderSection_iff J hY ((Q).objPreimage Z) s).1
      ((hX ((Q).objPreimage Z)).1 (h ((Q).objPreimage Z)))
    have hc : (fun f : Z ⟶ T ↦ f ≫ p) =
        b ∘ (fun f ↦ f ≫ p) ∘ a.symm := by
      funext f
      change f ≫ p = e.inv ≫ (e.hom ≫ f) ≫ p
      rw [Category.assoc, Iso.inv_hom_id_assoc]
    change Function.Bijective (fun f : Z ⟶ T ↦ f ≫ p)
    rw [hc]
    exact b.bijective.comp (ht.comp a.symm.bijective)
  · intro h X
    apply (hX X).2
    apply (bijective_precomp_cylinderSection_iff J hY X s).2
    exact (isIso_iff_yoneda_map_bijective _).1
      (isIso_toStalkwiseHomotopyCategory_map C _ h) ((Q).obj X)

end CategoryTheory.PointedSimplicialPresheaf
