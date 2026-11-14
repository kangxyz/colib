/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.ReducedHypercohomology
public import Colib.CategoryTheory.Sites.Simplicial.ReducedSuspensionCircle
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Shift.ShiftedHom

import Colib.CategoryTheory.Sites.Simplicial.ReducedCofiberExact
import Colib.CategoryTheory.Sites.Simplicial.ReducedConeChains
import Colib.CategoryTheory.Sites.Simplicial.ReducedConeInclusionMono
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# The simplicial circle boundary on reduced hypercohomology

Smashing with the native pointed simplicial circle gives the quotient of
the actual reduced cone by its base. The reduced cochains of this quotient
give the derived suspension isomorphism with its cofiber boundary map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Pretriangulated

universe d w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (Sheaf J AddCommGrpCat.{w})]

local notation "N" => (reducedCochains C J)
local notation "D" => (reducedDerivedChains C J)
local notation "S" => (pointedSimplicialCircle C)

omit [HasDerivedCategory (Sheaf J AddCommGrpCat.{w})] in
private theorem circleShortExact (X : PointedSimplicialPresheaf.{w} C) :
    ∃ h : (N).map (reducedConeInclusion X) ≫ (N).map (reducedConeToCircleSmash X) = 0,
      (ShortComplex.mk ((N).map (reducedConeInclusion X))
        ((N).map (reducedConeToCircleSmash X)) h).ShortExact := by
  let : Mono (reducedConeInclusion X).right := mono_reducedConeInclusion_right X
  exact exists_reducedCochains_shortExact_of_isPushout_isZero J
    (isPushout_reducedConeToCircleSmash X).flip (point_isZero C)

private theorem isZero_reducedDerivedChains_cone (X : PointedSimplicialPresheaf.{w} C) :
    IsZero ((D).obj (reducedCone X)) := by
  let e := ComplexShape.embeddingUpIntLE 0
  let E := e.extendFunctor (Sheaf J AddCommGrpCat.{w})
  let L := E.obj ((sheafifiedReducedChains C J).obj (reducedCone X))
  let Q : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ ⥤
      DerivedCategory (Sheaf J AddCommGrpCat.{w}) := DerivedCategory.Q
  have h := (sheafifiedReducedConeChainsContraction J X).extend e
  have h' : Homotopy (𝟙 L) 0 := by
    change Homotopy (E.map (𝟙 _)) (E.map 0) at h
    simpa only [Functor.map_id, Functor.map_zero] using h
  change IsZero (Q.obj L)
  apply (IsZero.iff_id_eq_zero _).2
  simpa only [Functor.map_id, Functor.map_zero] using
    DerivedCategory.Q_map_eq_of_homotopy (Sheaf J AddCommGrpCat.{w}) h'

/-- The connecting map of the reduced cochain sequence of the cone and its circle quotient. -/
@[no_expose]
def reducedCircleConnecting (X : PointedSimplicialPresheaf.{w} C) :
    ShiftedHom ((D).obj (Under.smash X S)) ((D).obj X) (1 : ℤ) := by
  unfold reducedDerivedChains
  exact DerivedCategory.triangleOfSESδ (circleShortExact J X).choose_spec

instance (X : PointedSimplicialPresheaf.{w} C) : IsIso (reducedCircleConnecting J X) := by
  unfold reducedCircleConnecting
  exact (Triangle.isZero₂_iff_isIso₃ _ (DerivedCategory.triangleOfSES_distinguished
    (circleShortExact J X).choose_spec)).1 (isZero_reducedDerivedChains_cone J X)

/-- The original simplicial circle connecting map is natural in the pointed presheaf. -/
@[reassoc]
theorem reducedCircleConnecting_naturality
    {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y) :
    (D).map (Under.smashMap f (𝟙 S)) ≫ reducedCircleConnecting J Y =
      reducedCircleConnecting J X ≫ ((D).map f)⟦(1 : ℤ)⟧' := by
  have hq : reducedConeToCircleSmash X ≫ Under.smashMap f (𝟙 S) =
      reducedConeMap f ≫ reducedConeToCircleSmash Y := by
    simp only [reducedConeToCircleSmash, reducedConeMap, Under.smashMap_comp,
      Category.id_comp, Category.comp_id]
  let m : ShortComplex.mk ((N).map (reducedConeInclusion X))
        ((N).map (reducedConeToCircleSmash X)) (circleShortExact J X).choose ⟶
      ShortComplex.mk ((N).map (reducedConeInclusion Y))
        ((N).map (reducedConeToCircleSmash Y)) (circleShortExact J Y).choose :=
    ShortComplex.homMk ((N).map f) ((N).map (reducedConeMap f))
      ((N).map (Under.smashMap f (𝟙 S)))
      (by simpa only [Functor.map_comp] using
        (N).congr_map (reducedConeInclusion_naturality f).symm)
      (by simpa only [Functor.map_comp] using (N).congr_map hq.symm)
  unfold reducedCircleConnecting reducedDerivedChains
  exact (DerivedCategory.triangleOfSESδ_naturality (circleShortExact J X).choose_spec
    (circleShortExact J Y).choose_spec m).symm

/-- Simplicial suspension in reduced cohomology, induced by the original cofiber boundary. -/
def reducedCircleSuspensionHomEquiv (X : PointedSimplicialPresheaf.{w} C)
    (K : DerivedCategory (Sheaf J AddCommGrpCat.{w})) (p : ℤ) :
    ShiftedHom ((D).obj X) K p ≃ ShiftedHom ((D).obj (Under.smash X S)) K (p + 1) := by
  let e := (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor _ (1 : ℤ))).homEquiv
    (X := (D).obj X) (Y := K⟦p⟧)
  let a := (asIso (reducedCircleConnecting J X)).symm.homFromEquiv
    (Z := (K⟦p⟧)⟦(1 : ℤ)⟧)
  let b := ((shiftFunctorAdd' _ p (1 : ℤ) (p + 1) rfl).app K).symm.homToEquiv
    (Z := (D).obj (Under.smash X S))
  exact e.trans (a.trans b)

/-- Simplicial suspension composes with the degree-one boundary in shifted Hom. -/
theorem reducedCircleSuspensionHomEquiv_apply (X : PointedSimplicialPresheaf.{w} C)
    (K : DerivedCategory (Sheaf J AddCommGrpCat.{w})) (p : ℤ)
    (x : ShiftedHom ((D).obj X) K p) :
    reducedCircleSuspensionHomEquiv J X K p x =
      (reducedCircleConnecting J X).comp x rfl := by
  simp only [reducedCircleSuspensionHomEquiv, Equiv.trans_apply, Iso.homToEquiv,
    Iso.homFromEquiv_apply, Iso.symm_inv, asIso_hom, Functor.FullyFaithful.homEquiv_apply]
  change (reducedCircleConnecting J X ≫ x⟦(1 : ℤ)⟧') ≫ _ = _
  exact Category.assoc _ _ _

/-- Simplicial suspension commutes with restriction of the pointed source. -/
theorem reducedCircleSuspensionHomEquiv_precomp
    {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf J AddCommGrpCat.{w})) (p : ℤ)
    (x : ShiftedHom ((D).obj Y) K p) :
    reducedCircleSuspensionHomEquiv J X K p ((D).map f ≫ x) =
      (D).map (Under.smashMap f (𝟙 S)) ≫ reducedCircleSuspensionHomEquiv J Y K p x := by
  simp only [reducedCircleSuspensionHomEquiv_apply, ShiftedHom.comp, Functor.map_comp,
    Category.assoc, reducedCircleConnecting_naturality_assoc]

end CategoryTheory.PointedSimplicialPresheaf

attribute [colib_tag "COL-1230"]
  CategoryTheory.PointedSimplicialPresheaf.reducedCircleConnecting
  CategoryTheory.PointedSimplicialPresheaf.reducedCircleSuspensionHomEquiv
  CategoryTheory.PointedSimplicialPresheaf.reducedCircleSuspensionHomEquiv_precomp

attribute [colib_ref "Voevodsky2003ReducedPowers" "Section 2, Theorem 2.4 and (2.7), p. 5"
  "ingredient" "Simplicial suspension on reduced cohomology via the cochain shift"]
  CategoryTheory.PointedSimplicialPresheaf.reducedCircleSuspensionHomEquiv
