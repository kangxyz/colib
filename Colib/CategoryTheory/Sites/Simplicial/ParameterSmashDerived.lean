/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.DerivedCategory.KInjectiveAdjunction
public import Colib.CategoryTheory.Sites.Simplicial.ParameterSmashHomotopy
import Colib.Algebra.Homology.DerivedCategory.KInjectiveHomNaturality
import Colib.CategoryTheory.Limits.PointedSmashFunctor
import Mathlib.Algebra.Category.Grp.AB
import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective.AdjointAndProducts

/-!
# Derived Hom from the reduced chains of a parameter smash

The original split cylinder comparison is localized on K-injective
coefficients. Exactness of the parameter coproduct and of
sheafification preserves K-injectivity on both ordinary presheaf targets.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe d d' w v u

namespace CategoryTheory.PointedSimplicialPresheaf

open ParameterCoproduct

private theorem trans_subtypeEquiv_apply_val
    {X Y Z T : Type*} {p : Z → Prop} {q : T → Prop}
    (e : X ≃ Y) (f : Y ≃ Subtype p) (g : Z ≃ T) (h : ∀ x, p x ↔ q (g x))
    (x : X) :
    ((e.trans (f.trans (g.subtypeEquiv h))) x).val = g (f (e x)).val := rfl

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max v w}]
  (V : C) (p : 𝟭 C ⟶ (Functor.const C).obj V)
  [HasDerivedCategory.{d} (Sheaf J AddCommGrpCat.{max v w})]
  [HasDerivedCategory.{d'} (Cᵒᵖ ⥤ AddCommGrpCat.{max v w})]

local notation "a" => ComplexShape.up ℤ
local notation "P" => reducedPresheafCochains C
local notation "R" => reducedCochains C J

/-- On a K-injective coefficient the actual derived maps from the
parameter smash are maps into reindexed ordinary presheaf cochains
whose restriction along the original point is zero. -/
@[no_expose]
def parameterSmashDerivedHomEquiv
    (X : PointedSimplicialPresheaf.{max v w} C)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{max v w}) ℤ) [I.IsKInjective] :
    let I₀ := liftedRepresentableInterval.{w} V
    let Y : PointedSimplicialPresheaf.{max v w} C :=
      Under.mk (show (⊤_ (Cᵒᵖ ⥤ SSet.{max v w})) ⟶ I₀ from
        liftedParameterPoint (C := C) V p)
    let W := parameterSmash X Y
    let D := Cᵒᵖ ⥤ AddCommGrpCat.{max v w}
    let Q : CochainComplex D ℤ ⥤ DerivedCategory D := DerivedCategory.Q
    let U := (sheafToPresheaf J AddCommGrpCat.{max v w}).mapHomologicalComplex a
    let T := (reindex V AddCommGrpCat.{max v w}).mapHomologicalComplex a
    let j := Q.map ((homologicalPointRestriction V _ p a).app (U.obj I))
    ((reducedDerivedChains C J).obj W ⟶ DerivedCategory.Q.obj I) ≃
      {f : Q.obj ((P).obj X) ⟶ Q.obj (T.obj (U.obj I)) // f ≫ j = 0} := by
  intro I₀ Y W D Q U T j
  let A := AddCommGrpCat.{max v w}
  let : AB4OfSize.{v} A := AB4OfSize_shrink.{v, w} A
  let F := sheafToPresheaf J A
  let G := presheafToSheaf J A
  let : CochainComplex.IsKInjective (U.obj I) :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact F G
      (sheafificationAdjunction J A) I
  let : CochainComplex.IsKInjective (T.obj (U.obj I)) :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact
      (reindex V A) (ParameterCoproduct.functor V A) (adjunction V A) (U.obj I)
  let e := CochainComplex.IsKInjective.localizedHomAddEquiv ((R).obj W) I
  let f := CochainComplex.IsKInjective.localizedHomAddEquiv ((P).obj X) (T.obj (U.obj I))
  let g := CochainComplex.IsKInjective.localizedHomAddEquiv ((P).obj X) (U.obj I)
  let H := HomotopyCategory.quotient D a
  let r := (homologicalPointRestriction V A p a).app (U.obj I)
  have h (x : H.obj ((P).obj X) ⟶ H.obj (T.obj (U.obj I))) :
      x ≫ H.map r = 0 ↔ f x ≫ j = 0 := by
    have h' : g (x ≫ H.map r) = f x ≫ j := by
      obtain ⟨y, rfl⟩ := H.map_surjective x
      have hg : g (H.map (y ≫ r)) = Q.map (y ≫ r) :=
        CochainComplex.IsKInjective.localizedHomAddEquiv_map _ _ _
      have hf : f (H.map y) = Q.map y :=
        CochainComplex.IsKInjective.localizedHomAddEquiv_map _ _ _
      rw [← H.map_comp, hg, hf]
      exact Q.map_comp y r
    rw [← h', ← g.map_zero]
    exact ⟨congrArg g, fun h => g.injective h⟩
  exact e.symm.toEquiv.trans ((parameterSmashHomotopyHomEquiv J V p X I).trans
    (f.toEquiv.subtypeEquiv h))

set_option maxHeartbeats 450000 in
-- Compare both localized Hom maps in the chosen pointed presheaf category.
/-- The original derived parameter comparison retains precomposition by
the actual maps of pointed smash products. -/
theorem parameterSmashDerivedHomEquiv_precomp
    {X Y : PointedSimplicialPresheaf.{max v w} C} (f : X ⟶ Y)
    (I : CochainComplex (Sheaf J AddCommGrpCat.{max v w}) ℤ) [I.IsKInjective] :
    let I₀ := liftedRepresentableInterval.{w} V
    let B : PointedSimplicialPresheaf.{max v w} C :=
      Under.mk (show (⊤_ (Cᵒᵖ ⥤ SSet.{max v w})) ⟶ I₀ from
        liftedParameterPoint (C := C) V p)
    let F := Under.smashRightFunctor (C := Cᵒᵖ ⥤ SSet.{max v w}) B
    let h : parameterSmash X B ⟶ parameterSmash Y B := F.map f
    ∀ g : (reducedDerivedChains C J).obj (parameterSmash Y B) ⟶ DerivedCategory.Q.obj I,
      (parameterSmashDerivedHomEquiv J V p X I
        ((reducedDerivedChains C J).map h ≫ g)).val =
      DerivedCategory.Q.map ((P).map f) ≫ (parameterSmashDerivedHomEquiv J V p Y I g).val := by
  intro I₀ B _F h g
  let A := AddCommGrpCat.{max v w}
  let : AB4OfSize.{v} A := AB4OfSize_shrink.{v, w} A
  let U := sheafToPresheaf J A
  let F := presheafToSheaf J A
  let M := (U.mapHomologicalComplex a).obj I
  let T := (reindex V A).mapHomologicalComplex a
  let H := HomotopyCategory.quotient (Sheaf J A) a
  let Q := HomotopyCategory.quotient (Cᵒᵖ ⥤ A) a
  let : CochainComplex.IsKInjective M :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact U F
      (sheafificationAdjunction J A) I
  let : CochainComplex.IsKInjective (T.obj M) :=
    CochainComplex.isKInjective_mapHomologicalComplex_of_exact
      (reindex V A) (ParameterCoproduct.functor V A) (adjunction V A) M
  let g₀ := (CochainComplex.IsKInjective.localizedHomAddEquiv
    ((R).obj (parameterSmash Y B)) I).symm g
  let Wₓ := parameterSmash X B
  let Wᵧ := parameterSmash Y B
  let h' := H.map ((R).map h)
  let Fₓ := parameterSmashHomotopyHomEquiv J V p X I
  let Fᵧ := parameterSmashHomotopyHomEquiv J V p Y I
  let eₓ := CochainComplex.IsKInjective.localizedHomAddEquiv ((R).obj Wₓ) I
  let eᵧ := CochainComplex.IsKInjective.localizedHomAddEquiv ((R).obj Wᵧ) I
  let Eₓ := CochainComplex.IsKInjective.localizedHomAddEquiv ((P).obj X) (T.obj M)
  let Eᵧ := CochainComplex.IsKInjective.localizedHomAddEquiv ((P).obj Y) (T.obj M)
  let m := (reducedDerivedChains C J).map h ≫ g
  have h₁ : (CochainComplex.IsKInjective.localizedHomAddEquiv
      ((R).obj Wₓ) I).symm m = h' ≫ g₀ :=
    CochainComplex.IsKInjective.localizedHomAddEquiv_symm_precomp ((R).map h) g
  have h₂ : (Fₓ (h' ≫ g₀)).val = Q.map ((P).map f) ≫ (Fᵧ g₀).val :=
    parameterSmashHomotopyHomEquiv_precomp J V p f I g₀
  have hX : (parameterSmashDerivedHomEquiv J V p X I m).val =
      Eₓ ((Fₓ (eₓ.symm m)).val) := by
    unfold parameterSmashDerivedHomEquiv
    exact trans_subtypeEquiv_apply_val eₓ.symm.toEquiv Fₓ Eₓ.toEquiv _ m
  have hY : (parameterSmashDerivedHomEquiv J V p Y I g).val =
      Eᵧ ((Fᵧ (eᵧ.symm g)).val) := by
    unfold parameterSmashDerivedHomEquiv
    exact trans_subtypeEquiv_apply_val eᵧ.symm.toEquiv Fᵧ Eᵧ.toEquiv _ g
  change (parameterSmashDerivedHomEquiv J V p X I m).val = _
  calc
    _ = Eₓ ((Fₓ (eₓ.symm m)).val) := hX
    _ = Eₓ ((Fₓ (h' ≫ g₀)).val) :=
      congrArg (fun z => Eₓ (Fₓ z).val) h₁
    _ = Eₓ (Q.map ((P).map f) ≫ (Fᵧ g₀).val) := congrArg Eₓ h₂
    _ = DerivedCategory.Q.map ((P).map f) ≫ Eᵧ ((Fᵧ g₀).val) :=
      CochainComplex.IsKInjective.localizedHomAddEquiv_precomp ((P).map f) _
    _ = _ := congrArg (DerivedCategory.Q.map ((P).map f) ≫ ·) hY.symm

end CategoryTheory.PointedSimplicialPresheaf
