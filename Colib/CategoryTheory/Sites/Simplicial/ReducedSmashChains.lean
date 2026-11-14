/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicTopology.SimplicialObject.AlexanderWhitney
public import Colib.CategoryTheory.Sites.Simplicial.ReducedSmashTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.AddCommGrpCatTransported
public import StacksFrontier.CategoryTheory.Monoidal.FunctorCategoryTensorColimits
public import StacksFrontier.CategoryTheory.Sites.CharacterTwistEquivalence
import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
import Mathlib.CategoryTheory.Sites.Limits
import StacksFrontier.Algebra.Homology.MapBifunctorNatIso
import StacksFrontier.CategoryTheory.Sites.MonoidalPreadditive

/-!
# The Alexander–Whitney map for reduced sheaf chains

Reduced free abelianization of a smash gives the degreewise tensor.
After sheafification the native Alexander–Whitney map compares its
alternating face complex with the tensor of the two alternating face
complexes. The native Moore homotopy equivalences give the comparison
on the normalized models.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology Opposite

attribute [local instance] AddCommGrpCat.monoidalCategory AddCommGrpCat.monoidalClosed
  AddCommGrpCat.braidedCategory AddCommGrpCat.uliftIntEquivalenceInverseMonoidal

universe u v

namespace CategoryTheory.PointedSimplicialPresheaf

/-- Bilinearity for the actual integral tensor of abelian groups. -/
theorem integralGroupsMonoidalPreadditive : MonoidalPreadditive AddCommGrpCat.{v + 1} := by
  let F := (AddCommGrpCat.uliftIntEquivalence.{v + 1}).inverse
  let : F.Additive := F.additive_of_preserves_binary_products
  exact monoidalPreadditive_of_faithful F

attribute [local instance] integralGroupsMonoidalPreadditive

variable {C : Type u} [Category.{v + 1} C]
  [UnivLE.{max u (v + 1), v + 1}] (J : GrothendieckTopology C)

/-- Abelian sheafification inverts the tensor of local isomorphisms. -/
theorem integralSheafificationMonoidal :
    (J.W (A := AddCommGrpCat.{v + 1})).IsMonoidal :=
  AddCommGrpCat.isMonoidal_W J

attribute [local instance] integralSheafificationMonoidal Sheaf.monoidalCategory

variable [HasSheafify J AddCommGrpCat.{v + 1}]

/-- The actual tensor of abelian sheaves is bilinear. -/
theorem integralSheavesMonoidalPreadditive :
    MonoidalPreadditive (Sheaf J AddCommGrpCat.{v + 1}) :=
  Sheaf.monoidalPreadditive J

attribute [local instance] integralSheavesMonoidalPreadditive

local notation "A" => Sheaf J AddCommGrpCat

/-- In each chain degree only the finite antidiagonal contributes to the tensor. -/
theorem integralSheafChainHasTensor (K M : ChainComplex (Sheaf J AddCommGrpCat.{v + 1}) ℕ) :
    HomologicalComplex.HasTensor K M :=
  HomologicalComplex₂.hasTotal_of_finite _ _ (fun n => Set.Finite.subset
    (Set.Finite.ofFinset (Finset.antidiagonal n) (fun _ => Finset.mem_antidiagonal))
    (fun _ h => h.1))

attribute [local instance] integralSheafChainHasTensor

local notation "L" => sheafifiedReducedFreeAbelian C J

/-- The monoidal sheafification comparison on the actual reduced smash. -/
@[no_expose]
def sheafifiedReducedSmashTensorIso (X Y : PointedSimplicialPresheaf.{v + 1} C) :
    (L).obj (Under.smash X Y) ≅ (L).obj X ⊗ (L).obj Y := by
  let F := (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj
    (presheafToSheaf J AddCommGrpCat.{v + 1})
  exact F.mapIso (reducedSmashTensorIso X Y) ≪≫
    (Functor.Monoidal.μIso F ((reducedFreeAbelian C).obj X) ((reducedFreeAbelian C).obj Y)).symm

/-- The sheafified tensor comparison retains both original pointed maps. -/
@[reassoc]
theorem sheafifiedReducedSmashTensorIso_naturality
    {X X' Y Y' : PointedSimplicialPresheaf.{v + 1} C} (f : X ⟶ X') (g : Y ⟶ Y') :
    (L).map (Under.smashMap f g) ≫ (sheafifiedReducedSmashTensorIso J X' Y').hom =
      (sheafifiedReducedSmashTensorIso J X Y).hom ≫ ((L).map f ⊗ₘ (L).map g) := by
  let F := (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj
    (presheafToSheaf J AddCommGrpCat.{v + 1})
  let R := reducedFreeAbelian.{v + 1} C
  let x := reducedSmashTensorIso X Y
  let y := reducedSmashTensorIso X' Y'
  let d := Functor.OplaxMonoidal.δ F
  have h := reducedSmashTensorIso_naturality f g
  have hδ := Functor.OplaxMonoidal.δ_natural F (R.map f) (R.map g)
  change F.map (R.map (Under.smashMap f g)) ≫ F.map y.hom ≫ d (R.obj X') (R.obj Y') =
    (F.map x.hom ≫ d (R.obj X) (R.obj Y)) ≫ (F.map (R.map f) ⊗ₘ F.map (R.map g))
  rw [← F.map_comp_assoc, h, F.map_comp, Category.assoc, Category.assoc, hδ]

private abbrev normalizedToAlternating (M : SimplicialObject A) :
    HomotopyEquiv ((normalizedMooreComplex A).obj M)
      ((alternatingFaceMapComplex A).obj M) :=
  DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex

/-- The actual reduced Alexander–Whitney map after passing to the
native normalized Moore complexes in both factors. -/
@[no_expose]
def reducedSmashAlexanderWhitney (X Y : PointedSimplicialPresheaf.{v + 1} C) :
    (normalizedMooreComplex A).obj ((L).obj (Under.smash X Y)) ⟶
      HomologicalComplex.tensorObj (C := A) (c := .down ℕ)
        ((normalizedMooreComplex A).obj ((L).obj X))
        ((normalizedMooreComplex A).obj ((L).obj Y)) :=
  (normalizedToAlternating J ((L).obj (Under.smash X Y))).hom ≫
    (alternatingFaceMapComplex A).map (sheafifiedReducedSmashTensorIso J X Y).hom ≫
    alexanderWhitney ((L).obj X) ((L).obj Y) ≫
    HomologicalComplex.tensorHom (C := A) (c := .down ℕ)
      (normalizedToAlternating J ((L).obj X)).inv
      (normalizedToAlternating J ((L).obj Y)).inv

set_option maxHeartbeats 400000 in
-- Keep the homotopy terms in their actual tensor complexes.
private def tensorHomotopyEquiv {K K' M M' : ChainComplex A ℕ}
    (e : HomotopyEquiv K K') (f : HomotopyEquiv M M') :
    HomotopyEquiv (HomologicalComplex.tensorObj K M) (HomologicalComplex.tensorObj K' M') where
  hom := HomologicalComplex.tensorHom e.hom f.hom
  inv := HomologicalComplex.tensorHom e.inv f.inv
  homotopyHomInvId := by
    have hc : HomologicalComplex.tensorHom e.hom f.hom ≫
        HomologicalComplex.tensorHom e.inv f.inv =
      HomologicalComplex.tensorHom (e.hom ≫ e.inv) (f.hom ≫ f.inv) :=
      (HomologicalComplex.mapBifunctorMap_comp _ _ _ _ _ _)
    rw [hc, ← tensorHom_id_id K M]
    exact (HomologicalComplex.mapBifunctorMapHomotopy₁ e.homotopyHomInvId
      (f.hom ≫ f.inv) (curriedTensor A) (.down ℕ)).trans
      (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 K) f.homotopyHomInvId
        (curriedTensor A) (.down ℕ))
  homotopyInvHomId := by
    have hc : HomologicalComplex.tensorHom e.inv f.inv ≫
        HomologicalComplex.tensorHom e.hom f.hom =
      HomologicalComplex.tensorHom (e.inv ≫ e.hom) (f.inv ≫ f.hom) :=
      (HomologicalComplex.mapBifunctorMap_comp _ _ _ _ _ _)
    rw [hc, ← tensorHom_id_id K' M']
    exact (HomologicalComplex.mapBifunctorMapHomotopy₁ e.homotopyInvHomId
      (f.inv ≫ f.hom) (curriedTensor A) (.down ℕ)).trans
      (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 K') f.homotopyInvHomId
        (curriedTensor A) (.down ℕ))

/-- The normalized comparison is a quasi-isomorphism on the actual
Nisnevich sheaf chains, and works for any site with the stated sheafification. -/
theorem quasiIso_reducedSmashAlexanderWhitney (X Y : PointedSimplicialPresheaf.{v + 1} C) :
    QuasiIso (reducedSmashAlexanderWhitney J X Y) := by
  let e := normalizedToAlternating J ((L).obj X)
  let f := normalizedToAlternating J ((L).obj Y)
  let g := normalizedToAlternating J ((L).obj (Under.smash X Y))
  let t := tensorHomotopyEquiv J e f
  let : QuasiIso g.hom := g.quasiIso_hom
  let : QuasiIso t.inv := t.quasiIso_inv
  let : QuasiIso (alexanderWhitney ((L).obj X) ((L).obj Y)) :=
    quasiIso_alexanderWhitney _ _
  change QuasiIso (g.hom ≫
    (alternatingFaceMapComplex A).map (sheafifiedReducedSmashTensorIso J X Y).hom ≫
      alexanderWhitney ((L).obj X) ((L).obj Y) ≫ t.inv)
  infer_instance

end CategoryTheory.PointedSimplicialPresheaf

attribute [colib_tag "COL-1234"]
  CategoryTheory.PointedSimplicialPresheaf.reducedSmashAlexanderWhitney
  CategoryTheory.PointedSimplicialPresheaf.quasiIso_reducedSmashAlexanderWhitney
  CategoryTheory.PointedSimplicialPresheaf.sheafifiedReducedSmashTensorIso_naturality

attribute [colib_ref "Voevodsky2003ReducedPowers" "Section 2, (2.3) and (2.9), pp. 4–5"
  "ingredient" "Reduced chains of the smash used in the exterior-product comparison"]
  CategoryTheory.PointedSimplicialPresheaf.reducedSmashAlexanderWhitney
