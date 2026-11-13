/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.ParameterCochainAdjunction

/-!
# The parameter-point summand

A natural family of maps into the parameter selects one of the
original coproduct summands. Its transpose restricts along the
actual graph of that family.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v z w

namespace CategoryTheory.PointedSimplicialPresheaf.ParameterCoproduct

variable {C : Type u} [Category.{v} C] (V : C)
  (p : 𝟭 C ⟶ (Functor.const C).obj V)
  (A : Type z) [Category.{w} A] [HasCoproducts.{v} A]

/-- The inclusion of the summand indexed by the original parameter point. -/
def pointInclusion : 𝟭 (Cᵒᵖ ⥤ A) ⟶ functor V A where
  app P :=
    { app := fun U => ι V A P U (p.app U.unop)
      naturality := fun {U W} f => by
        have h : f.unop ≫ p.app U.unop = p.app W.unop := by
          have hn := p.naturality f.unop
          change f.unop ≫ p.app U.unop = p.app W.unop ≫ 𝟙 V at hn
          exact hn.trans (Category.comp_id _)
        exact (congrArg (fun g => P.map f ≫ ι V A P W g) h.symm).trans
          (ι_restriction V A P f (p.app U.unop)).symm }
  naturality := fun {P Q} f => by
    apply NatTrans.ext
    funext U
    exact (ι_map_app V A f U (p.app U.unop)).symm

variable [HasBinaryProducts C]

/-- The graph of the parameter point in the original categorical product. -/
def pointGraph : 𝟭 C ⟶ prod.functor.flip.obj V where
  app U := prod.lift (𝟙 U) (p.app U)
  naturality := fun {U W} f => by
    have h : f ≫ p.app W = p.app U := by
      have hn := p.naturality f
      change f ≫ p.app W = p.app U ≫ 𝟙 V at hn
      exact hn.trans (Category.comp_id _)
    change f ≫ prod.lift (𝟙 W) (p.app W) =
      prod.lift (𝟙 U) (p.app U) ≫ prod.map f (𝟙 V)
    apply prod.hom_ext
    · simp
    · have h₁ : (f ≫ prod.lift (𝟙 W) (p.app W)) ≫ prod.snd = f ≫ p.app W :=
        (Category.assoc _ _ _).trans (congrArg (f ≫ ·) (prod.lift_snd _ _))
      have h₂ :
          (prod.lift (𝟙 U) (p.app U) ≫ prod.map f (𝟙 V)) ≫ prod.snd = p.app U := by
        rw [Category.assoc, prod.map_snd, ← Category.assoc, prod.lift_snd]
        exact Category.comp_id _
      exact h₁.trans (h.trans h₂.symm)

omit [HasCoproducts.{v} A] in
/-- Restrict a reindexed coefficient along the original parameter point. -/
def pointRestriction (p : 𝟭 C ⟶ (Functor.const C).obj V) :
    reindex V A ⟶ 𝟭 (Cᵒᵖ ⥤ A) where
  app P :=
    { app := fun U => P.map ((pointGraph V p).app U.unop).op
      naturality := fun {U W} f => by
        let G := prod.functor.flip.obj V
        let j := NatTrans.op (pointGraph V p)
        change P.map (G.op.map f) ≫ P.map (j.app W) = P.map (j.app U) ≫ P.map f
        rw [← P.map_comp, ← P.map_comp]
        exact P.congr_map (j.naturality f) }
  naturality := fun {P Q} f => by
    apply NatTrans.ext
    funext U
    let t := ((pointGraph V p).app U.unop).op
    change f.app _ ≫ Q.map t = P.map t ≫ f.app U
    exact (f.naturality t).symm

/-- The actual parameter-point summand transposes to restriction on its graph. -/
theorem pointInclusion_homEquiv_symm {P Q : Cᵒᵖ ⥤ A}
    (f : P ⟶ (reindex V A).obj Q) :
    (pointInclusion V p A).app P ≫ ((adjunction V A).homEquiv P Q).symm f =
      f ≫ (pointRestriction V A p).app Q := by
  apply NatTrans.ext
  funext U
  exact ι_homEquiv_symm_app V A f U.unop (p.app U.unop)

variable [Abelian A]

/-- Include the original parameter-point summand in each simplicial degree. -/
abbrev simplicialPointInclusion :
    𝟭 (SimplicialObject (Cᵒᵖ ⥤ A)) ⟶ simplicialFunctor V A :=
  (SimplicialObject.whiskering _ _).map (pointInclusion V p A)

/-- Include the original parameter-point summand in each cochain degree. -/
def homologicalPointInclusion {ι : Type*} (c : ComplexShape ι) :
    𝟭 (HomologicalComplex (Cᵒᵖ ⥤ A) c) ⟶ (functor V A).mapHomologicalComplex c :=
  (Functor.mapHomologicalComplexIdIso _ c).inv ≫ (pointInclusion V p A).mapHomologicalComplex c

omit [HasCoproducts.{v} A] in
/-- Restrict the original reindexed cochains to the parameter point degreewise. -/
def homologicalPointRestriction (p : 𝟭 C ⟶ (Functor.const C).obj V)
    {ι : Type*} (c : ComplexShape ι) :
    (reindex V A).mapHomologicalComplex c ⟶ 𝟭 (HomologicalComplex (Cᵒᵖ ⥤ A) c) :=
  (pointRestriction V A p).mapHomologicalComplex c ≫ (Functor.mapHomologicalComplexIdIso _ c).hom

/-- The same transpose identifies precomposition by the point summand
with postcomposition by point restriction on homotopy classes. -/
theorem homotopy_pointInclusion_homEquiv_symm
    (K I : CochainComplex (Cᵒᵖ ⥤ A) ℤ) :
    let c := ComplexShape.up ℤ
    let Q := HomotopyCategory.quotient (Cᵒᵖ ⥤ A) c
    let a := (adjunction V A).mapHomotopyCategoryAdjunction c
    let s := Q.map ((homologicalPointInclusion V p A c).app K)
    let r := Q.map ((homologicalPointRestriction V A p c).app I)
    ∀ f : Q.obj K ⟶ ((reindex V A).mapHomotopyCategory c).obj (Q.obj I),
      s ≫ (a.homEquiv (Q.obj K) (Q.obj I)).symm f = f ≫ r := by
  intro c Q a s r f
  let adj := adjunction V A
  let b := adj.mapHomologicalComplexAdjunction c
  change Q.obj K ⟶ Q.obj (((reindex V A).mapHomologicalComplex c).obj I) at f
  obtain ⟨g, rfl⟩ := Q.map_surjective f
  have hsymm : (a.homEquiv (Q.obj K) (Q.obj I)).symm (Q.map g) =
      Q.map ((b.homEquiv K I).symm g) := rfl
  have hg : (homologicalPointInclusion V p A c).app K ≫ (b.homEquiv K I).symm g =
      g ≫ (homologicalPointRestriction V A p c).app I := by
    apply HomologicalComplex.hom_ext
    intro n
    change (𝟙 _ ≫ (pointInclusion V p A).app (K.X n)) ≫
        (adj.homEquiv (K.X n) (I.X n)).symm (g.f n) =
      g.f n ≫ ((pointRestriction V A p).app (I.X n) ≫ 𝟙 _)
    rw [Category.id_comp, Category.comp_id]
    exact pointInclusion_homEquiv_symm V p A (g.f n)
  rw [hsymm, ← Q.map_comp, ← Q.map_comp]
  exact Q.congr_map hg

end CategoryTheory.PointedSimplicialPresheaf.ParameterCoproduct

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C] (V : C)
  (p : 𝟭 C ⟶ (Functor.const C).obj V)

/-- The global point in the lifted discrete Yoneda presheaf associated
to the original natural family of maps into the parameter. -/
def liftedParameterPoint (p : 𝟭 C ⟶ (Functor.const C).obj V) :
    (⊤_ (Cᵒᵖ ⥤ SSet.{max v w})) ⟶ liftedRepresentableInterval.{w} V where
  app U :=
    { app := fun _ => ↾fun _ => ULift.up (p.app U.unop)
      naturality := fun {n m} f => by
        apply ConcreteCategory.hom_ext
        intro x
        rfl }
  naturality := fun {U W} f => by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    change ULift.up (p.app W.unop) = ULift.up (f.unop ≫ p.app U.unop)
    have h := p.naturality f.unop
    change f.unop ≫ p.app U.unop = p.app W.unop ≫ 𝟙 V at h
    exact congrArg ULift.up (h.trans (Category.comp_id _)).symm

open ParameterCoproduct in
/-- The actual cylinder section enters the summand labelled by the
parameter point in each degree of reduced abelianization. -/
theorem reducedFreeAbelianParameterCylinderIso_hom_point
    (X : PointedSimplicialPresheaf.{max v w} C) :
    (reducedFreeAbelian C).map (cylinderSection X
        (show (⊤_ (Cᵒᵖ ⥤ SSet.{max v w})) ⟶ liftedRepresentableInterval.{w} V from
          liftedParameterPoint (C := C) V p)) ≫
        (reducedFreeAbelianParameterCylinderIso.{w} V X).hom =
      (simplicialPointInclusion V p _).app ((reducedFreeAbelian C).obj X) := by
  let I := liftedRepresentableInterval.{w} V
  let Y := parameterizedCylinder X I
  let i : (⊤_ (Cᵒᵖ ⥤ SSet.{max v w})) ⟶ I := liftedParameterPoint (C := C) V p
  let j := cylinderSection X i
  let R := reducedFreeAbelian.{max v w} C
  let e := reducedFreeAbelianParameterCylinderIso.{w} V X
  apply reduction_hom_ext C
  change reduction C X ≫ R.map j ≫ e.hom =
    reduction C X ≫ (simplicialPointInclusion V p _).app (R.obj X)
  rw [reduction_naturality_assoc]
  apply NatTrans.ext
  funext n
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro x
  let a : X.right ⟶ X.right ⨯ I := prod.lift (𝟙 X.right) (terminal.from X.right ≫ i)
  let b := pushout.inl (intervalAxis X I) (terminal.from I)
  let y := (a.app U).app n x
  have h₁ : (((prod.fst : X.right ⨯ I ⟶ X.right).app U).app n) y = x := by
    have h : a ≫ (prod.fst : X.right ⨯ I ⟶ X.right) = 𝟙 _ := prod.lift_fst _ _
    exact congrArg (fun f : X.right ⟶ X.right => (f.app U).app n x) h
  have h₂ : (((prod.snd : X.right ⨯ I ⟶ I).app U).app n y).down = p.app U.unop := by
    have h : a ≫ (prod.snd : X.right ⨯ I ⟶ I) = terminal.from X.right ≫ i :=
      prod.lift_snd _ _
    exact congrArg (fun f : X.right ⟶ I => ((f.app U).app n x).down) h
  have h := reducedFreeAbelianParameterCylinderIso_hom_generator.{w} V X n U y
  dsimp only at h
  change ((e.hom.app n).app U)
      (reducedGenerator C Y n U ((b.app U).app n y)) = _
  calc
    _ = ι V _ ((R.obj X).obj n) U (p.app U.unop) (reducedGenerator C X n U x) := by
      rw [h, h₁, h₂]
    _ = _ := rfl

end CategoryTheory.PointedSimplicialPresheaf
