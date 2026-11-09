/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.FiberedCategory.CocartesianSectionComposition
public import Colib.CategoryTheory.FiberedCategory.GrothendieckFiberTransport

/-!
# Original coefficient comparison for cocartesian evaluation

The coefficient comparison retains the actual identity-to-arrow section transition and the
literal reindex/evaluation equality. Its coherence comes from the actual section functor laws.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Functor
open CategoryTheory.StrictSections
universe u v u' v'
namespace CategoryTheory.GrothendieckSections
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})

/-- Identity evaluation after restriction is the actual coefficient fiber evaluation. -/
theorem originalFiberEvaluation_reindex {R S : C} (f : R ⟶ S) :
    underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f ⋙
        underCocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) S =
      cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
        (Under.forget R) (Under.mk f) := by
  change cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
      (Under.forget R) (Under.mk (f ≫ 𝟙 S)) = _
  let H : (R ⟶ S) →
      (underCocartesian (Pseudofunctor.Grothendieck.forget F) R ⥤
        Functor.Fiber (Pseudofunctor.Grothendieck.forget F) S) :=
    fun h => cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
      (Under.forget R) (Under.mk h)
  exact congrArg H (Category.comp_id f)

/-- The actual reindexed initial arrow is the coefficient arrow after identity-object transport. -/
theorem initialArrow_reindex_transport {R S T : C} (f : R ⟶ S) (g : S ⟶ T) :
    eqToHom (congrArg Under.mk (Category.comp_id f).symm) ≫
        (Under.map f).map (initialArrow S (Under.mk g)) =
      (Under.homMk g : Under.mk f ⟶ Under.mk (f ≫ g)) := by
  apply Under.UnderMorphism.ext
  change (Under.forget R).map
    (eqToHom (congrArg Under.mk (Category.comp_id f).symm)) ≫ g = g
  rw [eqToHom_map]
  simp

/-- Original coefficient evaluation uses the actual section transition and actual base transport. -/
def originalCoefficientIso {R S : C} (f : R ⟶ S) :
    underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f ⋙
        originalEvaluation F S ≅
      originalEvaluation F R ⋙ (F.map f.toLoc).toFunctor :=
  eqToIso (originalEvaluation_reindex F R f) ≪≫
    (originalEvaluationTransitionIso F R (Under.mk f)).symm

/-- The forward comparison uses the actual evaluation transport and inverse section transition. -/
theorem originalCoefficientIso_hom_app {R S : C} (f : R ⟶ S)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) :
    (originalCoefficientIso F f).hom.app s =
      (eqToIso (originalEvaluation_reindex F R f)).hom.app s ≫
        (originalEvaluationTransitionIso F R (Under.mk f)).inv.app s := rfl

/-- The inverse comparison is the literal transition followed by the actual evaluation transport. -/
theorem originalCoefficientIso_inv_app {R S : C} (f : R ⟶ S)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) :
    (originalCoefficientIso F f).inv.app s =
      originalTransition F R s (Under.mk f) ≫
        (eqToIso (originalEvaluation_reindex F R f)).inv.app s := rfl

/-- The reindexed transition is the actual coefficient arrow after the original source transport. -/
theorem originalTransition_reindex_source {R S T : C} (f : R ⟶ S) (g : S ⟶ T)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) :
    (F.map g.toLoc).toFunctor.map ((eqToIso (originalEvaluation_reindex F R f)).inv.app s) ≫
        originalTransition F S
          ((underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f).obj s)
          (Under.mk g) =
      originalArrowTransition F R s
        (Under.homMk g : Under.mk f ⟶ Under.mk (f ≫ g)) := by
  let x₀ := (cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
    (Under.forget R) (Under.mk f)).obj s
  let x₁ := (underCocartesianEvaluation (Pseudofunctor.Grothendieck.forget F) S).obj
    ((underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f).obj s)
  let y := (cocartesianEvaluation (Pseudofunctor.Grothendieck.forget F)
    (Under.forget R) (Under.mk (f ≫ g))).obj s
  let e : x₁ = x₀ := congrArg (fun G => G.obj s) (originalFiberEvaluation_reindex F f)
  let a := (Under.map f).map (initialArrow S (Under.mk g))
  let b : Under.mk f ⟶ Under.mk (f ≫ g) := Under.homMk g
  let φ : x₁.val ⟶ y.val := s.obj.val.map a
  let ψ : x₀.val ⟶ y.val := s.obj.val.map b
  have ha : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian g φ := s.property a
  have hb : (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian g ψ := s.property b
  have he : eqToHom (congrArg Subtype.val e.symm) =
      s.obj.val.map (eqToHom (congrArg Under.mk (Category.comp_id f).symm)) := by
    rw [eqToHom_map]
    rfl
  have hm : eqToHom (congrArg Subtype.val e.symm) ≫ φ = ψ := by
    exact (congrArg (fun k => k ≫ φ) he).trans
      ((s.obj.val.map_comp
        (eqToHom (congrArg Under.mk (Category.comp_id f).symm)) a).symm.trans
        (congrArg s.obj.val.map (initialArrow_reindex_transport f g)))
  have hn := GrothendieckFiber.liftedMap_precomp_eqToHom F g
    (x := x₀) (x' := x₁) (y := y) e.symm φ
  have hc := GrothendieckFiber.liftedMap_congr F g (x := x₀) (y := y)
    (eqToHom (congrArg Subtype.val e.symm) ≫ φ) ψ hm
  rw [← originalArrowTransition_initial F S
    ((underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f).obj s) (Under.mk g),
    originalArrowTransition_reindex]
  simp only [eqToIso.inv, eqToHom_app]
  exact hn.symm.trans hc

/-- The original inverse coefficient comparisons retain the genuine composition constraint. -/
theorem originalCoefficientIso_comp {R S T : C} (f : R ⟶ S) (g : S ⟶ T) :
    whiskerLeft (originalEvaluation F R) (F.mapComp f.toLoc g.toLoc).hom.toNatTrans ≫
        (Functor.associator (originalEvaluation F R)
          (F.map f.toLoc).toFunctor (F.map g.toLoc).toFunctor).inv ≫
        whiskerRight (originalCoefficientIso F f).inv (F.map g.toLoc).toFunctor ≫
        (Functor.associator
          (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
          (originalEvaluation F S) (F.map g.toLoc).toFunctor).hom ≫
        whiskerLeft (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
          (originalCoefficientIso F g).inv ≫
        (Functor.associator
          (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
          (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g)
          (originalEvaluation F T)).inv =
      (originalCoefficientIso F (f ≫ g)).inv ≫
        eqToHom (congrArg (fun G => G ⋙ originalEvaluation F T)
          (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g)) := by
  apply NatTrans.ext
  funext s
  let rf := underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f
  let rg := underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g
  let rfg := underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) (f ≫ g)
  let x : F.obj ⟨R⟩ := (originalEvaluation F R).obj s
  let y : F.obj ⟨S⟩ := (originalEvaluationAt F R (Under.mk f)).obj s
  let y' : F.obj ⟨S⟩ := (originalEvaluation F S).obj (rf.obj s)
  let z : F.obj ⟨T⟩ := (originalEvaluationAt F R (Under.mk (f ≫ g))).obj s
  let z' : F.obj ⟨T⟩ := (originalEvaluation F T).obj (rfg.obj s)
  let w : F.obj ⟨T⟩ := (originalEvaluation F T).obj (rg.obj (rf.obj s))
  let Pf : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩ := (F.map f.toLoc).toFunctor
  let Pg : F.obj ⟨S⟩ ⥤ F.obj ⟨T⟩ := (F.map g.toLoc).toFunctor
  let Pfg : F.obj ⟨R⟩ ⥤ F.obj ⟨T⟩ := (F.map (f ≫ g).toLoc).toFunctor
  let a : Pfg.obj x ⟶ z := originalTransition F R s (Under.mk (f ≫ g))
  let b : Pf.obj x ⟶ y := originalTransition F R s (Under.mk f)
  let c : Pg.obj y ⟶ z := originalArrowTransition F R s
    (Under.homMk g : Under.mk f ⟶ Under.mk (f ≫ g))
  let b' : Pg.obj y' ⟶ z := originalTransition F S (rf.obj s) (Under.mk g)
  let μ : Pfg.obj x ⟶ Pg.obj (Pf.obj x) :=
    (F.mapComp f.toLoc g.toLoc).hom.toNatTrans.app x
  let d₀ : y ⟶ y' := (eqToIso (originalEvaluation_reindex F R f)).inv.app s
  let d : z ⟶ w := (eqToIso (originalEvaluation_reindex F S g)).inv.app (rf.obj s)
  let e : z ⟶ z' := (eqToIso (originalEvaluation_reindex F R (f ≫ g))).inv.app s
  let q : z' ⟶ w := (eqToHom (congrArg (fun G => G ⋙ originalEvaluation F T)
    (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g))).app s
  have hsrc : Pg.map d₀ ≫ b' = c := originalTransition_reindex_source F f g s
  have hcomp : a = μ ≫ Pg.map b ≫ c := originalTransition_comp F R f g s
  have hd : d = e ≫ q := by
    dsimp only [d, e, q]
    simp only [eqToIso.inv, eqToHom_app, eqToHom_trans]
    rfl
  change μ ≫ (𝟙 _) ≫ Pg.map (b ≫ d₀) ≫ (𝟙 _) ≫ (b' ≫ d) ≫ (𝟙 _) =
    (a ≫ e) ≫ q
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hsrc]
  rw [← reassoc_of% hcomp, hd]

/-- The actual two-coefficient route, retaining every original comparison and associator. -/
def originalCoefficientRouteIso {R S T : C} (f : R ⟶ S) (g : S ⟶ T) :
    (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f ⋙
      underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g) ⋙
        originalEvaluation F T ≅
      originalEvaluation F R ⋙ (F.map f.toLoc).toFunctor ⋙ (F.map g.toLoc).toFunctor :=
  Functor.associator
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g)
      (originalEvaluation F T) ≪≫
    isoWhiskerLeft (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
      (originalCoefficientIso F g) ≪≫
    (Functor.associator
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
      (originalEvaluation F S) (F.map g.toLoc).toFunctor).symm ≪≫
    isoWhiskerRight (originalCoefficientIso F f) (F.map g.toLoc).toFunctor ≪≫
    Functor.associator (originalEvaluation F R)
      (F.map f.toLoc).toFunctor (F.map g.toLoc).toFunctor

private theorem forward_of_inverse_route {D : Type*} [Category D]
    {X Y Z W : D} (a : X ≅ Y) (m : Y ⟶ Z) (r : W ≅ Z) (e : X ⟶ W)
    (h : m ≫ r.inv = a.inv ≫ e) : a.hom ≫ m = e ≫ r.hom := by
  apply (cancel_mono r.inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  simp only [Iso.hom_inv_id_assoc]

/-- Forward coefficient comparisons satisfy the original two-route composition equation. -/
@[colib_tag "COL-0356",
  colib_ref "quillen"
    "Quillen/Aglib/CategoryTheory/FiberedCategory/CocartesianEvaluationCoherence.lean"
    "adaptation" "Actual Grothendieck section transition and coefficient coherence"]
theorem originalCoefficientIso_comp_hom {R S T : C} (f : R ⟶ S) (g : S ⟶ T) :
    (originalCoefficientIso F (f ≫ g)).hom ≫
        whiskerLeft (originalEvaluation F R) (F.mapComp f.toLoc g.toLoc).hom.toNatTrans =
      eqToHom (congrArg (fun G => G ⋙ originalEvaluation F T)
        (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g)) ≫
          (originalCoefficientRouteIso F f g).hom := by
  have h : whiskerLeft (originalEvaluation F R)
        (F.mapComp f.toLoc g.toLoc).hom.toNatTrans ≫
          (originalCoefficientRouteIso F f g).inv =
      (originalCoefficientIso F (f ≫ g)).inv ≫
        eqToHom (congrArg (fun G => G ⋙ originalEvaluation F T)
          (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g)) := by
    simpa only [originalCoefficientRouteIso, Iso.trans_inv, Iso.symm_inv,
      isoWhiskerLeft_inv, isoWhiskerRight_inv, Category.assoc] using
        (originalCoefficientIso_comp F f g)
  exact forward_of_inverse_route (originalCoefficientIso F (f ≫ g)) _
    (originalCoefficientRouteIso F f g) _ h

/-- At the identity coefficient, the original extracted transition is the geometric unit. -/
theorem originalTransition_id (R : C)
    (s : underCocartesian (Pseudofunctor.Grothendieck.forget F) R) :
    originalTransition F R s (Under.mk (𝟙 R)) =
      (F.mapId ⟨R⟩).hom.toNatTrans.app ((originalEvaluation F R).obj s) :=
  originalArrowTransition_id F R s (Under.mk (𝟙 R))

/-- The inverse coefficient comparison preserves the genuine pseudofunctor identity constraint. -/
theorem originalCoefficientIso_id (R : C) :
    (originalCoefficientIso F (𝟙 R)).inv ≫
        eqToHom (congrArg (fun G => G ⋙ originalEvaluation F R)
          (underCocartesianReindex_id (Pseudofunctor.Grothendieck.forget F) R)) ≫
        (Functor.leftUnitor (originalEvaluation F R)).hom =
      whiskerLeft (originalEvaluation F R) (F.mapId ⟨R⟩).hom.toNatTrans ≫
        (Functor.rightUnitor (originalEvaluation F R)).hom := by
  apply NatTrans.ext
  funext s
  let x : F.obj ⟨R⟩ := (originalEvaluation F R).obj s
  let y : F.obj ⟨R⟩ := (originalEvaluation F R).obj
    ((underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) (𝟙 R)).obj s)
  let P : F.obj ⟨R⟩ ⥤ F.obj ⟨R⟩ := (F.map (𝟙 R).toLoc).toFunctor
  let τ : P.obj x ⟶ x := originalTransition F R s (Under.mk (𝟙 R))
  let μ : P.obj x ⟶ x := (F.mapId ⟨R⟩).hom.toNatTrans.app x
  let e : x ⟶ y := (eqToIso (originalEvaluation_reindex F R (𝟙 R))).inv.app s
  let q : y ⟶ x := (eqToHom (congrArg (fun G => G ⋙ originalEvaluation F R)
    (underCocartesianReindex_id (Pseudofunctor.Grothendieck.forget F) R))).app s
  have hτ : τ = μ := originalTransition_id F R s
  let h₁ : x = y := congrArg (fun G => G.obj s)
    (originalEvaluation_reindex F R (𝟙 R)).symm
  let h₂ : y = x := congrArg (fun G => G.obj s)
    (congrArg (fun G => G ⋙ originalEvaluation F R)
      (underCocartesianReindex_id (Pseudofunctor.Grothendieck.forget F) R))
  have he₁ : e = eqToHom h₁ := by
    dsimp only [e]
    rw [eqToIso.inv, eqToHom_app]
    rfl
  have he₂ : q = eqToHom h₂ := by
    dsimp only [q]
    rw [eqToHom_app]
  have he : e ≫ q = 𝟙 x := by
    rw [he₁, he₂, eqToHom_trans]
    rfl
  change (τ ≫ e) ≫ q ≫ (𝟙 x) = μ ≫ (𝟙 x)
  simp only [Category.assoc, Category.comp_id, he, hτ]

end CategoryTheory.GrothendieckSections
