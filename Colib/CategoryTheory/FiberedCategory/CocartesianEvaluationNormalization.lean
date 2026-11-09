/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.FiberedCategory.CocartesianEvaluationCoherence

/-!
# Original evaluation coherence after target normalization

The original coefficient comparisons are followed by specified genuine target isomorphisms.
Their two-route equation follows from the proved section equation and ordinary naturality.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Functor
open CategoryTheory.StrictSections
universe u v u' v'
namespace CategoryTheory.GrothendieckSections
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})

/-- Follow the original coefficient comparison by the actual target normalization iso. -/
def normalizedCoefficientIso {R S : C} (f : R ⟶ S)
    {N : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} (n : (F.map f.toLoc).toFunctor ≅ N) :
    underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f ⋙
        originalEvaluation F S ≅ originalEvaluation F R ⋙ N :=
  originalCoefficientIso F f ≪≫ isoWhiskerLeft (originalEvaluation F R) n

/-- The original pseudofunctor constraint with the same three target normalizations. -/
def normalizedCoefficientCompIso {R S T : C} (f : R ⟶ S) (g : S ⟶ T)
    {Nf : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} {Ng : F.obj ⟨S⟩ ⥤ F.obj ⟨T⟩}
    {Nfg : F.obj ⟨R⟩ ⥤ F.obj ⟨T⟩}
    (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng)
    (nfg : (F.map (f ≫ g).toLoc).toFunctor ≅ Nfg) : Nfg ≅ Nf ⋙ Ng :=
  nfg.symm ≪≫ Cat.Hom.toNatIso (F.mapComp f.toLoc g.toLoc) ≪≫
    isoWhiskerRight nf (F.map g.toLoc).toFunctor ≪≫ isoWhiskerLeft Nf ng

/-- The forward constraint is exactly the three normalizations and original comparison. -/
theorem normalizedCoefficientCompIso_hom {R S T : C} (f : R ⟶ S) (g : S ⟶ T)
    {Nf : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} {Ng : F.obj ⟨S⟩ ⥤ F.obj ⟨T⟩}
    {Nfg : F.obj ⟨R⟩ ⥤ F.obj ⟨T⟩}
    (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng)
    (nfg : (F.map (f ≫ g).toLoc).toFunctor ≅ Nfg) :
    (normalizedCoefficientCompIso F f g nf ng nfg).hom =
      nfg.inv ≫ (F.mapComp f.toLoc g.toLoc).hom.toNatTrans ≫
        whiskerRight nf.hom (F.map g.toLoc).toFunctor ≫ whiskerLeft Nf ng.hom := rfl

/-- The two actual normalized coefficient comparisons retain their original associators. -/
def normalizedCoefficientRouteIso {R S T : C} (f : R ⟶ S) (g : S ⟶ T)
    {Nf : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} {Ng : F.obj ⟨S⟩ ⥤ F.obj ⟨T⟩}
    (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng) :
    (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f ⋙
      underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g) ⋙
        originalEvaluation F T ≅ originalEvaluation F R ⋙ Nf ⋙ Ng :=
  Functor.associator
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g)
      (originalEvaluation F T) ≪≫
    isoWhiskerLeft (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
      (normalizedCoefficientIso F g ng) ≪≫
    (Functor.associator
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f)
      (originalEvaluation F S) Ng).symm ≪≫
    isoWhiskerRight (normalizedCoefficientIso F f nf) Ng ≪≫
    Functor.associator (originalEvaluation F R) Nf Ng

/-- Genuine target normalization preserves the proved original coefficient composition equation. -/
@[colib_tag "COL-0356",
  colib_ref "quillen"
    "Quillen/Aglib/CategoryTheory/FiberedCategory/CocartesianEvaluationNormalization.lean"
    "adaptation" "Actual Grothendieck section transition and coefficient coherence"]
theorem normalizedCoefficientIso_comp_hom {R S T : C} (f : R ⟶ S) (g : S ⟶ T)
    {Nf : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩} {Ng : F.obj ⟨S⟩ ⥤ F.obj ⟨T⟩}
    {Nfg : F.obj ⟨R⟩ ⥤ F.obj ⟨T⟩}
    (nf : (F.map f.toLoc).toFunctor ≅ Nf) (ng : (F.map g.toLoc).toFunctor ≅ Ng)
    (nfg : (F.map (f ≫ g).toLoc).toFunctor ≅ Nfg) :
    (normalizedCoefficientIso F (f ≫ g) nfg).hom ≫
        whiskerLeft (originalEvaluation F R) (normalizedCoefficientCompIso F f g nf ng nfg).hom =
      eqToHom (congrArg (fun G => G ⋙ originalEvaluation F T)
        (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g)) ≫
          (normalizedCoefficientRouteIso F f g nf ng).hom := by
  apply NatTrans.ext
  funext s
  let rf := underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f
  let rg := underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) g
  let rfg := underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) (f ≫ g)
  let x : F.obj ⟨R⟩ := (originalEvaluation F R).obj s
  let y : F.obj ⟨S⟩ := (originalEvaluation F S).obj (rf.obj s)
  let z : F.obj ⟨T⟩ := (originalEvaluation F T).obj (rg.obj (rf.obj s))
  let z' : F.obj ⟨T⟩ := (originalEvaluation F T).obj (rfg.obj s)
  let Pf : F.obj ⟨R⟩ ⥤ F.obj ⟨S⟩ := (F.map f.toLoc).toFunctor
  let Pg : F.obj ⟨S⟩ ⥤ F.obj ⟨T⟩ := (F.map g.toLoc).toFunctor
  let Pfg : F.obj ⟨R⟩ ⥤ F.obj ⟨T⟩ := (F.map (f ≫ g).toLoc).toFunctor
  let a : z' ⟶ Pfg.obj x := (originalCoefficientIso F (f ≫ g)).hom.app s
  let b : y ⟶ Pf.obj x := (originalCoefficientIso F f).hom.app s
  let c : z ⟶ Pg.obj y := (originalCoefficientIso F g).hom.app (rf.obj s)
  let μ : Pfg.obj x ⟶ Pg.obj (Pf.obj x) :=
    (F.mapComp f.toLoc g.toLoc).hom.toNatTrans.app x
  let e : z' ⟶ z := (eqToHom (congrArg (fun G => G ⋙ originalEvaluation F T)
    (underCocartesianReindex_comp (Pseudofunctor.Grothendieck.forget F) f g))).app s
  have h : a ≫ μ = e ≫ c ≫ Pg.map b := by
    have h := congrArg (fun t => t.app s) (originalCoefficientIso_comp_hom F f g)
    change a ≫ μ = e ≫ ((𝟙 _) ≫ c ≫ (𝟙 _) ≫ Pg.map b ≫ (𝟙 _)) at h
    simpa only [Category.id_comp, Category.comp_id] using h
  change (a ≫ nfg.hom.app x) ≫
      (nfg.inv.app x ≫ μ ≫ Pg.map (nf.hom.app x) ≫ ng.hom.app (Nf.obj x)) =
    e ≫ ((𝟙 _) ≫ (c ≫ ng.hom.app y) ≫ (𝟙 _) ≫ Ng.map (b ≫ nf.hom.app x) ≫ (𝟙 _))
  simp only [Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% h]
  rw [ng.hom.naturality, ng.hom.naturality_assoc]

/-- The actual normalized identity constraint retains the original pseudofunctor unit. -/
def normalizedCoefficientIdIso (R : C)
    {N : F.obj ⟨R⟩ ⥤ F.obj ⟨R⟩} (n : (F.map (𝟙 R).toLoc).toFunctor ≅ N) :
    N ≅ 𝟭 (F.obj ⟨R⟩) :=
  n.symm ≪≫ Cat.Hom.toNatIso (F.mapId ⟨R⟩)

/-- The normalized unit retains precisely the normalization inverse and original unit. -/
theorem normalizedCoefficientIdIso_hom (R : C)
    {N : F.obj ⟨R⟩ ⥤ F.obj ⟨R⟩} (n : (F.map (𝟙 R).toLoc).toFunctor ≅ N) :
    (normalizedCoefficientIdIso F R n).hom = n.inv ≫ (F.mapId ⟨R⟩).hom.toNatTrans := rfl

/-- Normalization preserves the genuine forward coefficient unit equation. -/
theorem normalizedCoefficientIso_id_hom (R : C)
    {N : F.obj ⟨R⟩ ⥤ F.obj ⟨R⟩} (n : (F.map (𝟙 R).toLoc).toFunctor ≅ N) :
    (normalizedCoefficientIso F (𝟙 R) n).hom ≫
        whiskerLeft (originalEvaluation F R) (normalizedCoefficientIdIso F R n).hom ≫
        (Functor.rightUnitor (originalEvaluation F R)).hom =
      eqToHom (congrArg (fun G => G ⋙ originalEvaluation F R)
        (underCocartesianReindex_id (Pseudofunctor.Grothendieck.forget F) R)) ≫
          (Functor.leftUnitor (originalEvaluation F R)).hom := by
  apply NatTrans.ext
  funext s
  let r := underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) (𝟙 R)
  let x : F.obj ⟨R⟩ := (originalEvaluation F R).obj s
  let y : F.obj ⟨R⟩ := (originalEvaluation F R).obj (r.obj s)
  let P : F.obj ⟨R⟩ ⥤ F.obj ⟨R⟩ := (F.map (𝟙 R).toLoc).toFunctor
  let a : y ≅ P.obj x := (originalCoefficientIso F (𝟙 R)).app s
  let μ : P.obj x ⟶ x := (F.mapId ⟨R⟩).hom.toNatTrans.app x
  let e : y ⟶ x := (eqToHom (congrArg (fun G => G ⋙ originalEvaluation F R)
    (underCocartesianReindex_id (Pseudofunctor.Grothendieck.forget F) R))).app s
  have h : a.inv ≫ e = μ := by
    have h := congrArg (fun t => t.app s) (originalCoefficientIso_id F R)
    change a.inv ≫ e ≫ (𝟙 x) = μ ≫ (𝟙 x) at h
    simpa only [Category.comp_id] using h
  change (a.hom ≫ n.hom.app x) ≫ (n.inv.app x ≫ μ) ≫ (𝟙 x) = e ≫ (𝟙 x)
  simp only [Category.assoc, Category.comp_id, Iso.hom_inv_id_app_assoc]
  rw [← h, Iso.hom_inv_id_assoc]

end CategoryTheory.GrothendieckSections
