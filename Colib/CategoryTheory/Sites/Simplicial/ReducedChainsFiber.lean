/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.CategoryTheory.Sites.Simplicial.ReducedChains
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseWeakEquivalence
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Stalks of reduced free simplicial abelian sheaves

At a point of the site, degreewise stalks of the sheafified reduced free abelian
object agree with reduction on the actual simplicial fiber. The comparison
commutes with the cokernel projection and with all simplicial operators.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (Φ : J.Point.{w})

/-- Take the native abelian sheaf fiber in every simplicial degree. -/
abbrev simplicialAbelianSheafFiber :
    SimplicialObject (Sheaf J AddCommGrpCat.{w}) ⥤ SimplicialObject AddCommGrpCat.{w} :=
  (Functor.whiskeringRight _ _ _).obj Φ.sheafFiber

/-- Apply free abelianization to every simplex of a simplicial set. -/
abbrev simplicialSetFreeAbelian : SSet.{w} ⥤ SimplicialObject AddCommGrpCat.{w} :=
  (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free

private abbrev simplicialAbelianPresheafFiber :
    SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ SimplicialObject AddCommGrpCat.{w} :=
  (Functor.whiskeringRight _ _ _).obj Φ.presheafFiber

private abbrev simplexEvaluation (n : SimplexCategoryᵒᵖ) : SSet.{w} ⥤ Type w :=
  (CategoryTheory.evaluation _ _).obj n

section LocallySmall

variable [LocallySmall.{w} C]

/-- The simplicial fiber of the terminal presheaf is terminal. -/
def isTerminalFiberTerminal :
    IsTerminal (Φ.presheafFiber.obj (⊤_ (Cᵒᵖ ⥤ SSet.{w}))) := by
  letI : PreservesFiniteLimits (Φ.presheafFiber (A := SSet.{w})) :=
    preservesFiniteLimits_of_evaluation _ fun n ↦ by
      let E := (CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type w)).obj n
      let : PreservesFiniteLimits ((Functor.whiskeringRight Cᵒᵖ SSet.{w} _).obj E) :=
        ⟨fun K _ _ ↦ inferInstance⟩
      exact preservesFiniteLimits_of_natIso (Φ.presheafFiberCompIso E)
  exact terminalIsTerminal.isTerminalObj Φ.presheafFiber _

/-- The unique simplex in the fiber of the terminal presheaf. -/
@[instance_reducible]
def fiberTerminalSimplexUnique (n : SimplexCategoryᵒᵖ) :
    Unique ((Φ.presheafFiber.obj (⊤_ (Cᵒᵖ ⥤ SSet.{w}))).obj n) :=
  Types.isTerminalEquivUnique _
    ((isTerminalFiberTerminal Φ).isTerminalObj ((CategoryTheory.evaluation _ (Type w)).obj n) _)

/-- The simplex supplied by the actual basepoint in the simplicial fiber. -/
def fiberBasepointSimplex (F : PointedSimplicialPresheaf.{w} C) (n : SimplexCategoryᵒᵖ) :
    ((fiberAtPoint C Φ).obj F).obj n :=
  (Φ.presheafFiber.map F.hom).app n (fiberTerminalSimplexUnique Φ n).default

/-- The germ of the global basepoint is the actual basepoint of the simplicial fiber. -/
theorem toPresheafFiber_basepointSimplex (F : PointedSimplicialPresheaf.{w} C)
    (n : SimplexCategoryᵒᵖ) (U : C) (x : Φ.fiber.obj U) :
    (Φ.toPresheafFiber U x F.right).app n (basepointSimplex C F n (op U)) =
      fiberBasepointSimplex Φ F n := by
  let := fiberTerminalSimplexUnique Φ n
  let t := (terminalSimplexUnique C n (op U)).default
  have h := congrArg (fun f ↦ f.app n t) (Φ.toPresheafFiber_naturality F.hom U x)
  change (Φ.presheafFiber.map F.hom).app n
      ((Φ.toPresheafFiber U x (⊤_ (Cᵒᵖ ⥤ SSet.{w}))).app n t) =
    (Φ.toPresheafFiber U x F.right).app n ((F.hom.app (op U)).app n t) at h
  exact h.symm.trans (congrArg (fun y ↦ (Φ.presheafFiber.map F.hom).app n y)
    (Subsingleton.elim _ _))

private def freeAbelianPresheafFiberIsoAt (P : Cᵒᵖ ⥤ SSet.{w}) (n : SimplexCategoryᵒᵖ) :
    ((simplicialAbelianPresheafFiber Φ).obj ((freeAbelian C).obj P)).obj n ≅
      ((simplicialSetFreeAbelian.{w}).obj (Φ.presheafFiber.obj P)).obj n :=
  (Φ.presheafFiberCompIso (simplexEvaluation n ⋙ AddCommGrpCat.free)).app P

private def freeAbelianPresheafFiberIsoApp (P : Cᵒᵖ ⥤ SSet.{w}) :
    (simplicialAbelianPresheafFiber Φ).obj ((freeAbelian C).obj P) ≅
      simplicialSetFreeAbelian.obj (Φ.presheafFiber.obj P) :=
  NatIso.ofComponents (freeAbelianPresheafFiberIsoAt Φ P) (by
    intro n m f
    let τ : simplexEvaluation n ⋙ AddCommGrpCat.free ⟶
        simplexEvaluation m ⋙ AddCommGrpCat.free :=
      Functor.whiskerRight ((CategoryTheory.evaluation _ _).map f) AddCommGrpCat.free
    apply Φ.presheafFiber_hom_ext
    intro U u
    change Φ.toPresheafFiber U u (P ⋙ (simplexEvaluation n ⋙ AddCommGrpCat.free)) ≫
        Φ.presheafFiber.map (Functor.whiskerLeft P τ) ≫
          (Φ.presheafFiberCompIso (simplexEvaluation m ⋙ AddCommGrpCat.free)).hom.app P =
      Φ.toPresheafFiber U u (P ⋙ (simplexEvaluation n ⋙ AddCommGrpCat.free)) ≫
        (Φ.presheafFiberCompIso (simplexEvaluation n ⋙ AddCommGrpCat.free)).hom.app P ≫
          τ.app (Φ.presheafFiber.obj P)
    rw [Φ.toPresheafFiber_naturality_assoc,
      Φ.toPresheafFiber_presheafFiberCompIso_hom_app,
      Φ.toPresheafFiber_presheafFiberCompIso_hom_app_assoc]
    exact (τ.naturality (Φ.toPresheafFiber U u P)).symm)

private def freeAbelianPresheafFiberIso :
    freeAbelian C ⋙ simplicialAbelianPresheafFiber Φ ≅
      Φ.presheafFiber ⋙ simplicialSetFreeAbelian.{w} :=
  NatIso.ofComponents (freeAbelianPresheafFiberIsoApp Φ) (by
    intro P Q f
    ext n : 1
    exact (Φ.presheafFiberCompIso (simplexEvaluation n ⋙ AddCommGrpCat.free)).hom.naturality f)

variable [HasSheafify J AddCommGrpCat.{w}]

/-- Sheafification followed by the native stalk, in each simplicial degree. -/
abbrev degreewiseSheafifyThenFiber :
    SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ SimplicialObject AddCommGrpCat.{w} :=
  (Functor.whiskeringRight _ _ _).obj (presheafToSheaf J AddCommGrpCat.{w} ⋙ Φ.sheafFiber)

/-- The sheafified free abelian presheaf has the free abelianization of the
actual simplicial fiber as its degreewise stalk. -/
@[no_expose]
def freeAbelianSheafFiberIso :
    freeAbelian C ⋙ degreewiseSheafifyThenFiber Φ ≅
      Φ.presheafFiber ⋙ simplicialSetFreeAbelian.{w} :=
  Functor.isoWhiskerLeft (freeAbelian C)
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).mapIso
      (Φ.presheafToSheafCompSheafFiberIso AddCommGrpCat.{w})) ≪≫
    freeAbelianPresheafFiberIso Φ

/-- The free abelian stalk comparison sends the sheafification of a free
abelian germ to the free abelian image of the corresponding simplicial germ. -/
@[reassoc]
theorem toPresheafFiber_comp_freeAbelianSheafFiberIso_hom
    (P : Cᵒᵖ ⥤ SSet.{w}) (n : SimplexCategoryᵒᵖ) (U : C) (x : Φ.fiber.obj U) :
    Φ.toPresheafFiber U x (((freeAbelian C).obj P).obj n) ≫
        Φ.presheafFiber.map (toSheafify J (((freeAbelian C).obj P).obj n)) ≫
          ((freeAbelianSheafFiberIso Φ).hom.app P).app n =
      AddCommGrpCat.free.map ((Φ.toPresheafFiber U x P).app n) := by
  let E := simplexEvaluation n ⋙ AddCommGrpCat.free
  let i := (Φ.presheafToSheafCompSheafFiberIso AddCommGrpCat.{w}).app (P ⋙ E)
  let e := (Φ.presheafFiberCompIso E).app P
  change Φ.toPresheafFiber U x (P ⋙ E) ≫ i.inv ≫ i.hom ≫ e.hom =
    E.map (Φ.toPresheafFiber U x P)
  rw [i.inv_hom_id_assoc]
  exact Φ.toPresheafFiber_presheafFiberCompIso_hom_app E U x P

end LocallySmall

/-- The free abelian image of the actual basepoint on the simplicial fiber. -/
def fiberBasepointArrow : PointedSimplicialPresheaf.{w} C ⥤
    Arrow (SimplicialObject AddCommGrpCat.{w}) where
  obj F := Arrow.mk (simplicialSetFreeAbelian.map (Φ.presheafFiber.map F.hom))
  map {F G} f := Arrow.homMk' (𝟙 _) (simplicialSetFreeAbelian.map ((fiberAtPoint C Φ).map f))
    (by
      rw [Category.id_comp]
      change simplicialSetFreeAbelian.map (Φ.presheafFiber.map G.hom) =
        simplicialSetFreeAbelian.map (Φ.presheafFiber.map F.hom) ≫
          simplicialSetFreeAbelian.map (Φ.presheafFiber.map f.right)
      rw [← Functor.map_comp, ← Functor.map_comp, Under.w f])
  map_id F := by
    apply Arrow.hom_ext
    · rfl
    · exact (fiberAtPoint C Φ ⋙ simplicialSetFreeAbelian).map_id F
  map_comp f g := by
    apply Arrow.hom_ext
    · exact (Category.id_comp _).symm
    · exact (fiberAtPoint C Φ ⋙ simplicialSetFreeAbelian).map_comp f g

/-- Reduced free abelianization of the actual pointed simplicial fiber. -/
def reducedFreeAbelianFiber : PointedSimplicialPresheaf.{w} C ⥤
    SimplicialObject AddCommGrpCat.{w} :=
  fiberBasepointArrow Φ ⋙ coker _

/-- The cokernel projection killing the free abelian image of the actual
basepoint of the simplicial fiber. -/
def fiberReduction (F : PointedSimplicialPresheaf.{w} C) :
    (Φ.presheafFiber ⋙ simplicialSetFreeAbelian).obj F.right ⟶
      (reducedFreeAbelianFiber Φ).obj F :=
  cokernel.π ((fiberBasepointArrow Φ).obj F).hom

@[reassoc (attr := simp)]
theorem fiberReduction_naturality {F G : PointedSimplicialPresheaf.{w} C} (f : F ⟶ G) :
    fiberReduction Φ F ≫ (reducedFreeAbelianFiber Φ).map f =
      (Φ.presheafFiber ⋙ simplicialSetFreeAbelian).map f.right ≫ fiberReduction Φ G :=
  ((coker.π _).naturality ((fiberBasepointArrow Φ).map f)).symm

section Sheafify

variable [LocallySmall.{w} C] [HasSheafify J AddCommGrpCat.{w}]

private def sheafifiedReducedFreeAbelianFiberIsoApp (F : PointedSimplicialPresheaf.{w} C) :
    (degreewiseSheafifyThenFiber Φ).obj ((reducedFreeAbelian C).obj F) ≅
      (reducedFreeAbelianFiber Φ).obj F :=
  PreservesCokernel.iso (degreewiseSheafifyThenFiber Φ) ((freeAbelian C).map F.hom) ≪≫
    cokernel.mapIso _ _ ((freeAbelianSheafFiberIso Φ).app _) ((freeAbelianSheafFiberIso Φ).app _)
      ((freeAbelianSheafFiberIso Φ).hom.naturality F.hom)

@[reassoc]
private theorem reduction_comp_sheafifiedReducedFreeAbelianFiberIsoApp_hom
    (F : PointedSimplicialPresheaf.{w} C) :
    (degreewiseSheafifyThenFiber Φ).map (reduction C F) ≫
        (sheafifiedReducedFreeAbelianFiberIsoApp Φ F).hom =
      (freeAbelianSheafFiberIso Φ).hom.app F.right ≫ fiberReduction Φ F := by
  let H := degreewiseSheafifyThenFiber Φ
  let a := (freeAbelian C).map F.hom
  let b := ((fiberBasepointArrow Φ).obj F).hom
  let e := freeAbelianSheafFiberIso Φ
  change H.map (cokernel.π a) ≫ (PreservesCokernel.iso H a).hom ≫
    (cokernel.mapIso (H.map a) b (e.app _) (e.app _) (e.hom.naturality F.hom)).hom = _
  rw [PreservesCokernel.π_iso_hom_assoc]
  exact cokernel.π_desc _ _ _

/-- Taking degreewise stalks of sheafified reduction agrees naturally with
reduction on the actual simplicial fiber. -/
@[no_expose]
def sheafifiedReducedFreeAbelianFiberIso :
    sheafifiedReducedFreeAbelian C J ⋙ simplicialAbelianSheafFiber Φ ≅
      reducedFreeAbelianFiber Φ :=
  NatIso.ofComponents (sheafifiedReducedFreeAbelianFiberIsoApp Φ) (by
    intro F G f
    have : Epi ((degreewiseSheafifyThenFiber Φ).map (reduction C F)) := by
      change Epi ((degreewiseSheafifyThenFiber Φ).map (cokernel.π ((freeAbelian C).map F.hom)))
      rw [← Iso.comp_inv_eq _ |>.2
        (PreservesCokernel.π_iso_hom (degreewiseSheafifyThenFiber Φ)
          ((freeAbelian C).map F.hom)).symm]
      infer_instance
    apply (cancel_epi ((degreewiseSheafifyThenFiber Φ).map (reduction C F))).1
    change (degreewiseSheafifyThenFiber Φ).map (reduction C F) ≫
        (degreewiseSheafifyThenFiber Φ).map ((reducedFreeAbelian C).map f) ≫
          (sheafifiedReducedFreeAbelianFiberIsoApp Φ G).hom =
      (degreewiseSheafifyThenFiber Φ).map (reduction C F) ≫
        (sheafifiedReducedFreeAbelianFiberIsoApp Φ F).hom ≫
          (reducedFreeAbelianFiber Φ).map f
    rw [← Functor.map_comp_assoc, reduction_naturality, Functor.map_comp_assoc,
      reduction_comp_sheafifiedReducedFreeAbelianFiberIsoApp_hom Φ G,
      reduction_comp_sheafifiedReducedFreeAbelianFiberIsoApp_hom_assoc Φ F,
      fiberReduction_naturality]
    exact (freeAbelianSheafFiberIso Φ).hom.naturality_assoc f.right (fiberReduction Φ G))

/-- The stalk comparison intertwines sheafified reduction with the actual
cokernel projection in the simplicial fiber. -/
@[reassoc]
theorem reduction_comp_sheafifiedReducedFreeAbelianFiberIso_hom
    (F : PointedSimplicialPresheaf.{w} C) :
    (degreewiseSheafifyThenFiber Φ).map (reduction C F) ≫
        (sheafifiedReducedFreeAbelianFiberIso Φ).hom.app F =
      (freeAbelianSheafFiberIso Φ).hom.app F.right ≫ fiberReduction Φ F :=
  reduction_comp_sheafifiedReducedFreeAbelianFiberIsoApp_hom Φ F

/-- In each degree the abelian sheaf stalk is the cokernel of free
abelianization of the actual fiber basepoint. -/
def sheafifiedReducedFreeAbelianFiberObjIso
    (F : PointedSimplicialPresheaf.{w} C) (n : SimplexCategoryᵒᵖ) :
    Φ.sheafFiber.obj (((sheafifiedReducedFreeAbelian C J).obj F).obj n) ≅
      cokernel (AddCommGrpCat.free.map ((Φ.presheafFiber.map F.hom).app n)) :=
  ((sheafifiedReducedFreeAbelianFiberIso Φ).app F).app n ≪≫
    PreservesCokernel.iso ((CategoryTheory.evaluation _ _).obj n)
      ((fiberBasepointArrow Φ).obj F).hom

/-- The degreewise stalk comparison sends the reduction map to the cokernel
projection after the free abelian stalk comparison. -/
@[reassoc]
theorem reduction_comp_sheafifiedReducedFreeAbelianFiberObjIso_hom
    (F : PointedSimplicialPresheaf.{w} C) (n : SimplexCategoryᵒᵖ) :
    Φ.sheafFiber.map ((presheafToSheaf J AddCommGrpCat.{w}).map ((reduction C F).app n)) ≫
        (sheafifiedReducedFreeAbelianFiberObjIso Φ F n).hom =
      ((freeAbelianSheafFiberIso Φ).hom.app F.right).app n ≫
        cokernel.π (AddCommGrpCat.free.map ((Φ.presheafFiber.map F.hom).app n)) := by
  let E := (CategoryTheory.evaluation SimplexCategoryᵒᵖ AddCommGrpCat.{w}).obj n
  let a := ((fiberBasepointArrow Φ).obj F).hom
  let e := PreservesCokernel.iso E a
  have h := NatTrans.congr_app (reduction_comp_sheafifiedReducedFreeAbelianFiberIso_hom Φ F) n
  change Φ.sheafFiber.map ((presheafToSheaf J _).map ((reduction C F).app n)) ≫
      ((sheafifiedReducedFreeAbelianFiberIso Φ).hom.app F).app n =
    ((freeAbelianSheafFiberIso Φ).hom.app F.right).app n ≫ E.map (fiberReduction Φ F) at h
  change Φ.sheafFiber.map ((presheafToSheaf J _).map ((reduction C F).app n)) ≫
      ((sheafifiedReducedFreeAbelianFiberIso Φ).hom.app F).app n ≫ e.hom =
    ((freeAbelianSheafFiberIso Φ).hom.app F.right).app n ≫ cokernel.π (E.map a)
  have hp : E.map (fiberReduction Φ F) ≫ e.hom = cokernel.π (E.map a) :=
    PreservesCokernel.π_iso_hom E a
  calc
    _ = (Φ.sheafFiber.map ((presheafToSheaf J _).map ((reduction C F).app n)) ≫
          ((sheafifiedReducedFreeAbelianFiberIso Φ).hom.app F).app n) ≫ e.hom :=
      (Category.assoc _ _ _).symm
    _ = (((freeAbelianSheafFiberIso Φ).hom.app F.right).app n ≫ E.map (fiberReduction Φ F)) ≫
        e.hom := congrArg (· ≫ e.hom) h
    _ = _ := (Category.assoc _ _ _).trans
      (congrArg (((freeAbelianSheafFiberIso Φ).hom.app F.right).app n ≫ ·) hp)

end Sheafify

end CategoryTheory.PointedSimplicialPresheaf

namespace CategoryTheory.PointedSimplicialPresheaf

attribute [colib_tag "COL-1011"]
  sheafifiedReducedFreeAbelianFiberIso
  sheafifiedReducedFreeAbelianFiberObjIso

end CategoryTheory.PointedSimplicialPresheaf
