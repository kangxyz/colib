/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.ParameterCylinderCochainPoint
public import Colib.CategoryTheory.Sites.Simplicial.ParameterCylinderSheafHomotopy
public import Colib.CategoryTheory.Sites.Simplicial.PointedParameterSmash
public import Colib.CategoryTheory.Sites.Simplicial.ParameterCylinderNaturality
import Colib.CategoryTheory.Limits.PointedSmashFunctor

/-!
# Homotopy maps from the reduced chains of a parameter smash

The original split cylinder quotient identifies homotopy maps from
the smash with maps into the reindexed presheaf complex that vanish
under the original point restriction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

section SplitQuotient

variable {B : Type*} [Category* B] [Preadditive B]
  (U : Type*) [Category* U] [HasZeroMorphisms U] (H : U ⥤ B) [H.PreservesZeroMorphisms]
  {C₁ C₂ C₃ : U} (i : C₁ ⟶ C₂) (q : C₂ ⟶ C₃)
  (r : C₂ ⟶ C₁) (s : C₃ ⟶ C₂)
  (hiq : i ≫ q = 0) (hsq : s ≫ q = 𝟙 C₃)
  (hdecomp : H.map r ≫ H.map i + H.map q ≫ H.map s = 𝟙 (H.obj C₂))

private def splitQuotientHomEquiv (M : B) : (H.obj C₃ ⟶ M) ≃
    {f : H.obj C₂ ⟶ M // H.map i ≫ f = 0} where
  toFun f := ⟨H.map q ≫ f, by
    rw [← Category.assoc, ← H.map_comp, hiq, H.map_zero, zero_comp]⟩
  invFun f := H.map s ≫ f.val
  left_inv f := by
    change H.map s ≫ H.map q ≫ f = f
    rw [← Category.assoc, ← H.map_comp, hsq, H.map_id, Category.id_comp]
  right_inv f := by
    apply Subtype.ext
    have h := congrArg (· ≫ f.val) hdecomp
    simpa only [Preadditive.add_comp, Category.assoc, f.property, comp_zero,
      zero_add, Category.id_comp] using h

end SplitQuotient

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max v w}]
  (V : C) (p : 𝟭 C ⟶ (Functor.const C).obj V)

local notation "a" => ComplexShape.up ℤ
local notation "P" => reducedPresheafCochains C
local notation "R" => reducedCochains C J

set_option synthInstance.maxHeartbeats 80000 in
-- Infer the finite limits and colimits of the actual presheaf category.
/-- The actual smash of two pointed presheaves in the same coefficient universe. -/
abbrev parameterSmash
    (X Y : PointedSimplicialPresheaf.{max v w} C) :
    PointedSimplicialPresheaf.{max v w} C :=
  Under.smash X Y

open ParameterCoproduct in
private def parameterCylinderHomotopyHomEquiv
    (X : PointedSimplicialPresheaf.{max v w} C)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{max v w}) ℤ) :
    let I₀ := liftedRepresentableInterval.{w} V
    let H := HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{max v w}) a
    let Q := HomotopyCategory.quotient (Cᵒᵖ ⥤ AddCommGrpCat.{max v w}) a
    let U := (sheafToPresheaf J AddCommGrpCat.{max v w}).mapHomologicalComplex a
    let T := (reindex V AddCommGrpCat.{max v w}).mapHomologicalComplex a
    (H.obj ((R).obj (parameterizedCylinder X I₀)) ⟶ H.obj I) ≃
      (Q.obj ((P).obj X) ⟶ Q.obj (T.obj (U.obj I))) := by
  intro I₀ H Q U T
  let D := reducedPresheafCochainsParameterCylinderIso.{w} V X
  let b := (adjunction V AddCommGrpCat.{max v w}).mapHomotopyCategoryAdjunction a
  exact (reducedCochainsHomotopyHomEquiv C J I (parameterizedCylinder X I₀)).trans
    (((Q.mapIso D).homCongr (Iso.refl _)).trans
      (b.homEquiv (Q.obj ((P).obj X)) (Q.obj (U.obj I))))

open ParameterCoproduct in
private theorem parameterCylinderHomotopyHomEquiv_precomp
    {X Y : PointedSimplicialPresheaf.{max v w} C} (f : X ⟶ Y)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{max v w}) ℤ) :
    let I₀ := liftedRepresentableInterval.{w} V
    let H := HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{max v w}) a
    let Q := HomotopyCategory.quotient (Cᵒᵖ ⥤ AddCommGrpCat.{max v w}) a
    let d := parameterizedCylinderMap f I₀
    ∀ g : H.obj ((R).obj (parameterizedCylinder Y I₀)) ⟶ H.obj I,
      parameterCylinderHomotopyHomEquiv J V X I (H.map ((R).map d) ≫ g) =
        Q.map ((P).map f) ≫ parameterCylinderHomotopyHomEquiv J V Y I g := by
  intro I₀ H Q d g
  let A := AddCommGrpCat.{max v w}
  let b := (adjunction V A).mapHomotopyCategoryAdjunction a
  let e := Q.mapIso (reducedPresheafCochainsParameterCylinderIso.{w} V X)
  let e' := Q.mapIso (reducedPresheafCochainsParameterCylinderIso.{w} V Y)
  let F := (ParameterCoproduct.functor V A).mapHomotopyCategory a
  let k := Q.map ((P).map f)
  let x := reducedCochainsHomotopyHomEquiv C J I (parameterizedCylinder X I₀)
  let y := reducedCochainsHomotopyHomEquiv C J I (parameterizedCylinder Y I₀)
  have hd : Q.map ((P).map d) ≫ e'.hom = e.hom ≫ F.map k := by
    change Q.map ((P).map d) ≫ Q.map (reducedPresheafCochainsParameterCylinderIso.{w} V Y).hom =
      Q.map (reducedPresheafCochainsParameterCylinderIso.{w} V X).hom ≫
        Q.map (((ParameterCoproduct.functor V A).mapHomologicalComplex a).map ((P).map f))
    rw [← Q.map_comp, ← Q.map_comp]
    exact Q.congr_map (reducedPresheafCochainsParameterCylinderIso_hom_naturality V f)
  have he : e.inv ≫ Q.map ((P).map d) = F.map k ≫ e'.inv := by
    apply (cancel_mono e'.hom).1
    simp only [Category.assoc, hd, e.inv_hom_id_assoc, e'.inv_hom_id]
    exact (Category.comp_id (F.map k)).symm
  have hx : x (H.map ((R).map d) ≫ g) = Q.map ((P).map d) ≫ y g :=
    reducedCochainsHomotopyHomEquiv_precomp C J I d g
  unfold parameterCylinderHomotopyHomEquiv
  change b.homEquiv _ _ (e.inv ≫ x (H.map ((R).map d) ≫ g) ≫ 𝟙 _) =
    k ≫ b.homEquiv _ _ (e'.inv ≫ y g ≫ 𝟙 _)
  rw [hx, Category.comp_id, Category.comp_id, ← Category.assoc e.inv, he, Category.assoc]
  exact b.homEquiv_naturality_left k _

open ParameterCoproduct in
/-- Homotopy maps from the reduced cochains of the actual parameter
smash are the homotopy maps into the actual point kernel. -/
@[no_expose]
def parameterSmashHomotopyHomEquiv
    (X : PointedSimplicialPresheaf.{max v w} C)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{max v w}) ℤ) :
    let I₀ := liftedRepresentableInterval.{w} V
    let Y : PointedSimplicialPresheaf.{max v w} C :=
      Under.mk (show (⊤_ (Cᵒᵖ ⥤ SSet.{max v w})) ⟶ I₀ from
        liftedParameterPoint (C := C) V p)
    let W := parameterSmash X Y
    let H := HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{max v w}) a
    let Q := HomotopyCategory.quotient (Cᵒᵖ ⥤ AddCommGrpCat.{max v w}) a
    let U := (sheafToPresheaf J AddCommGrpCat.{max v w}).mapHomologicalComplex a
    let T := (reindex V AddCommGrpCat.{max v w}).mapHomologicalComplex a
    let j := Q.map ((homologicalPointRestriction V _ p a).app (U.obj I))
    (H.obj ((R).obj W) ⟶ H.obj I) ≃
      {f : Q.obj ((P).obj X) ⟶ Q.obj (T.obj (U.obj I)) // f ≫ j = 0} := by
  intro I₀ Y W H Q U T j
  let Z := parameterizedCylinder X Y.right
  let s := cylinderSection X Y.hom
  let r := cylinderProjection X Y.right
  let q := cylinderToParameterSmash X Y
  let h := (exists_parameterSmashReducedCochains_shortExact X Y J).choose
  let hS := (exists_parameterSmashReducedCochains_shortExact X Y J).choose_spec
  let S := ShortComplex.mk ((R).map s) ((R).map q) h
  have hr : S.f ≫ (R).map r = 𝟙 S.X₁ :=
    ((R).map_comp s r).symm.trans
      (((R).congr_map (cylinderSection_projection X Y.hom)).trans ((R).map_id X))
  let e := ShortComplex.Splitting.ofExactOfRetraction S hS.exact ((R).map r) hr hS.epi_g
  have he : H.map e.r ≫ H.map S.f + H.map S.g ≫ H.map e.s = 𝟙 _ := by
    rw [← H.map_comp, ← H.map_comp, ← H.map_add, e.id, H.map_id]
  let E₁ := splitQuotientHomEquiv _ H S.f S.g e.r e.s h e.s_g he (H.obj I)
  let F (M : PointedSimplicialPresheaf.{max v w} C) := reducedCochainsHomotopyHomEquiv C J I M
  let D := reducedPresheafCochainsParameterCylinderIso.{w} V X
  let A := AddCommGrpCat.{max v w}
  let b := (adjunction V A).mapHomotopyCategoryAdjunction a
  let t := Q.map ((homologicalPointInclusion V p A a).app ((P).obj X))
  let F₀ := parameterCylinderHomotopyHomEquiv J V X I
  have ht : Q.map ((P).map s) ≫ Q.map D.hom = t :=
    (Q.map_comp _ _).symm.trans (Q.congr_map
      (reducedPresheafCochainsParameterCylinderIso_hom_point V p X))
  have hzero (M : PointedSimplicialPresheaf.{max v w} C) : F M 0 = 0 := by
    exact reducedCochainsHomotopyHomEquiv_zero C J I M
  have hcomp (f : H.obj ((R).obj Z) ⟶ H.obj I) :
      F X (H.map ((R).map s) ≫ f) = F₀ f ≫ j := by
    let g := F Z f
    let e' := Q.mapIso D
    let g' := e'.inv ≫ g
    have hg : (b.homEquiv (Q.obj ((P).obj X)) (Q.obj (U.obj I))).symm (F₀ f) = g' := by
      unfold F₀ parameterCylinderHomotopyHomEquiv
      change (b.homEquiv _ _).symm (b.homEquiv _ _ (e'.inv ≫ g ≫ 𝟙 _)) = g'
      rw [Equiv.symm_apply_apply, Category.comp_id]
    have hq : Q.map ((P).map s) ≫ g = t ≫ g' := by
      change _ = t ≫ e'.inv ≫ g
      calc
        _ = Q.map ((P).map s) ≫ Q.map D.hom ≫ e'.inv ≫ g :=
          congrArg (Q.map ((P).map s) ≫ ·) (e'.hom_inv_id_assoc g).symm
        _ = _ := (Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ e'.inv ≫ g) ht)
    calc
      _ = Q.map ((P).map s) ≫ g :=
        reducedCochainsHomotopyHomEquiv_precomp C J I s f
      _ = t ≫ g' := hq
      _ = _ := (congrArg (t ≫ ·) hg.symm).trans
        (homotopy_pointInclusion_homEquiv_symm V p A ((P).obj X) (U.obj I) (F₀ f))
  have hP (f : H.obj S.X₂ ⟶ H.obj I) :
      H.map S.f ≫ f = 0 ↔ F₀ f ≫ j = 0 := by
    change H.map ((R).map s) ≫ f = 0 ↔ F₀ f ≫ j = 0
    rw [← hcomp, ← hzero X]
    exact ⟨congrArg (F X), fun h => (F X).injective h⟩
  let A₁ := H.obj S.X₂ ⟶ H.obj I
  let A₂ := Q.obj ((P).obj X) ⟶ Q.obj (T.obj (U.obj I))
  let e₀ : A₁ ≃ A₂ := F₀
  let e' := e₀.subtypeEquiv (q := fun g : A₂ => g ≫ j = 0) hP
  exact E₁.trans e'

/-- The split Hom comparison is natural for the original pointed maps. -/
theorem parameterSmashHomotopyHomEquiv_precomp
    {X Y : PointedSimplicialPresheaf.{max v w} C} (f : X ⟶ Y)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{max v w}) ℤ) :
    let I₀ := liftedRepresentableInterval.{w} V
    let B : PointedSimplicialPresheaf.{max v w} C :=
      Under.mk (show (⊤_ (Cᵒᵖ ⥤ SSet.{max v w})) ⟶ I₀ from
        liftedParameterPoint (C := C) V p)
    let H := HomotopyCategory.quotient (Sheaf J AddCommGrpCat.{max v w}) a
    let Q := HomotopyCategory.quotient (Cᵒᵖ ⥤ AddCommGrpCat.{max v w}) a
    let F := Under.smashRightFunctor (C := Cᵒᵖ ⥤ SSet.{max v w}) B
    let h : parameterSmash X B ⟶ parameterSmash Y B := F.map f
    ∀ g : H.obj ((R).obj (parameterSmash Y B)) ⟶ H.obj I,
      (parameterSmashHomotopyHomEquiv J V p X I
        (H.map ((R).map h) ≫ g)).val =
      Q.map ((P).map f) ≫ (parameterSmashHomotopyHomEquiv J V p Y I g).val := by
  intro I₀ B H Q F h g
  let d := parameterizedCylinderMap f I₀
  let a₀ := H.map ((R).map (cylinderToParameterSmash X B))
  let b₀ := H.map ((R).map (cylinderToParameterSmash Y B))
  let f' := h
  have hq : a₀ ≫ H.map ((R).map f') = H.map ((R).map d) ≫ b₀ := by
    rw [← H.map_comp, ← H.map_comp, ← (R).map_comp, ← (R).map_comp]
    exact H.congr_map ((R).congr_map (cylinderToParameterSmash_naturality B f).symm)
  unfold parameterSmashHomotopyHomEquiv
  change parameterCylinderHomotopyHomEquiv J V X I
      (a₀ ≫ H.map ((R).map f') ≫ g) =
    Q.map ((P).map f) ≫ parameterCylinderHomotopyHomEquiv J V Y I (b₀ ≫ g)
  rw [← Category.assoc a₀, hq, Category.assoc]
  exact parameterCylinderHomotopyHomEquiv_precomp J V f I (b₀ ≫ g)

end CategoryTheory.PointedSimplicialPresheaf
