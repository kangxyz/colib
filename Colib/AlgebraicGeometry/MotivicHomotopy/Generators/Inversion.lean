/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.AffineLineLocalization
public import Colib.AlgebraicGeometry.MotivicHomotopy.Generators.Stalks
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Sheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Inversion of the actual geometric generating maps

The empty smooth scheme has the empty Nisnevich cover. The sheaf condition
therefore makes the ordinary map from the initial presheaf to its representable
a member of the native type-valued class `J.W`. The actual free-pointed
constant simplicial lift identifies this with the empty-descent generator on
site fibers.

The original affine-line interval localization functor consequently inverts
all three displayed families: empty descent, geometric Nisnevich squares,
and actual affine-line projections. This is an inversion statement for that
specified functor, not a comparison with a local model category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open CategoryTheory.PointedSimplicialPresheaf

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (S : Scheme.{u})

/-- The empty family covers the actual empty smooth scheme in the Nisnevich topology. -/
theorem bot_mem_nisnevichTopology_emptySmoothScheme :
    (⊥ : Sieve (emptySmoothScheme S)) ∈ nisnevichTopology S (emptySmoothScheme S) := by
  apply mem_nisnevichTopology_iff.mpr
  refine ⟨(⊥ : Presieve (emptySmoothScheme S)), ?_, bot_le⟩
  rw [mem_nisnevichPrecoverage_iff, Presieve.map_bot]
  change (⊥ : Presieve (emptySmoothScheme S).left) ∈
    Nisnevich.precoverage (emptySmoothScheme S).left
  rw [Nisnevich.mem_precoverage_iff]
  constructor
  · intro _ _ h
    cases h
  · intro x
    let : IsEmpty (emptySmoothScheme S).left := inferInstanceAs (IsEmpty (∅ : Scheme.{u}))
    exact isEmptyElim x

/-- The ordinary presheaf map whose freely pointed lift gives empty descent. -/
def emptyPresheafMap : (⊥_ ((SmoothSite S)ᵒᵖ ⥤ Type u)) ⟶
    CategoryTheory.yoneda.obj (emptySmoothScheme S) :=
  initial.to _

/-- Ordinary sheaves satisfy empty descent, so the exact ordinary empty map
belongs to the native sheafification class. -/
theorem W_emptyPresheafMap : (nisnevichTopology S).W (emptyPresheafMap S) := by
  intro F hF
  let hT : IsTerminal (F.obj (op (emptySmoothScheme S))) :=
    Sheaf.isTerminalOfBotCover (⟨F, hF⟩ : Sheaf (nisnevichTopology S) (Type u))
      (emptySmoothScheme S) (bot_mem_nisnevichTopology_emptySmoothScheme S)
  let : Unique (F.obj (op (emptySmoothScheme S))) := Types.isTerminalEquivUnique _ hT
  constructor
  · intro f g _
    apply yonedaEquiv.injective
    exact Subsingleton.elim _ _
  · intro f
    exact ⟨yonedaEquiv.symm default, initialIsInitial.hom_ext _ _⟩

/-- The freely pointed constant lift of the initial presheaf is the chosen point object. -/
def emptyDiscretePointIso :
    point.{u} (SmoothSite S) ≅ (discretePointedPresheafFunctor.{u} (SmoothSite S)).obj
      (⊥_ ((SmoothSite S)ᵒᵖ ⥤ Type u)) :=
  (point_isZero.{u} (SmoothSite S)).isoIsInitial
    (isColimitOfHasInitialOfPreservesColimit (discretePointedPresheafFunctor.{u} (SmoothSite S)))

set_option backward.isDefEq.respectTransparency false in
/-- The initial-object comparison retains the actual point-to-representable map. -/
@[reassoc]
theorem emptyDiscretePointIso_hom_map :
    (emptyDiscretePointIso S).hom ≫
        (discretePointedPresheafFunctor (SmoothSite S)).map (emptyPresheafMap S) =
      emptyDescentMap S :=
  (point_isZero (SmoothSite S)).eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
/-- Every actual Nisnevich site fiber sends the original empty-descent map to an isomorphism. -/
theorem isIso_fiberAtPoint_emptyDescentMap (Φ : (nisnevichTopology S).Point.{u}) :
    IsIso ((fiberAtPoint (SmoothSite S) Φ).map (emptyDescentMap S)) := by
  let : IsIso ((fiberAtPoint (SmoothSite S) Φ).map
      ((discretePointedPresheafFunctor (SmoothSite S)).map (emptyPresheafMap S))) :=
    isIso_fiberAtPoint_discretePointed_map_of_W (SmoothSite S) Φ _ (W_emptyPresheafMap S)
  rw [← emptyDiscretePointIso_hom_map S, Functor.map_comp]
  infer_instance

/-- The actual empty-descent generator is a stalkwise weak equivalence. -/
theorem stalkwiseWeakEquivalences_emptyDescentMap :
    stalkwiseWeakEquivalences (SmoothSite S) (nisnevichTopology S) (emptyDescentMap S) := by
  intro Φ
  let : IsIso ((fiberAtPoint (SmoothSite S) Φ).map (emptyDescentMap S)) :=
    isIso_fiberAtPoint_emptyDescentMap S Φ
  exact SSet.realizationWeakEquivalences_of_isIso _

/-- The empty-descent family is contained in the chosen stalkwise class. -/
theorem emptyDescentMaps_le_stalkwiseWeakEquivalences :
    emptyDescentMaps S ≤ stalkwiseWeakEquivalences (SmoothSite S) (nisnevichTopology S) := by
  rintro _ _ _ ⟨_⟩
  exact stalkwiseWeakEquivalences_emptyDescentMap S

variable (R : CommRingCat.{u})

/-- The original affine-line localization functor inverts every stalkwise weak equivalence. -/
theorem isIso_toAffineLineHomotopyCategory_map_of_stalkwise
    {F G : PointedSimplicialPresheaf.{u} (SmoothSite (Spec R))} (f : F ⟶ G)
    (hf : stalkwiseWeakEquivalences (SmoothSite (Spec R)) (nisnevichTopology (Spec R)) f) :
    IsIso ((toAffineLineHomotopyCategory R).map f) :=
  (intervalWeakEquivalences _ _ (affineLineParameter R)).Q_inverts f
    (stalkwiseWeakEquivalences_le_intervalWeakEquivalences _ _ (affineLineParameter R) f hf)

/-- The original functor inverts the actual empty-descent generator. -/
theorem isIso_toAffineLineHomotopyCategory_map_emptyDescentMap :
    IsIso ((toAffineLineHomotopyCategory R).map (emptyDescentMap (Spec R))) :=
  isIso_toAffineLineHomotopyCategory_map_of_stalkwise R _
    (stalkwiseWeakEquivalences_emptyDescentMap (Spec R))

/-- The original functor inverts each actual geometric Nisnevich square map. -/
theorem isIso_toAffineLineHomotopyCategory_map_nisnevichSquareMap
    (Q : NisnevichSquare (Spec R)) :
    IsIso ((toAffineLineHomotopyCategory R).map (nisnevichSquareMap (Spec R) Q)) :=
  isIso_toAffineLineHomotopyCategory_map_of_stalkwise R _
    (stalkwiseWeakEquivalences_nisnevichSquareMap (Spec R) Q)

/-- The exact selected localization functor inverts all three actual generating families. -/
theorem motivicGeneratingMaps_isInvertedBy_toAffineLineHomotopyCategory :
    (motivicGeneratingMaps R).IsInvertedBy (toAffineLineHomotopyCategory R) := by
  intro _ _ f hf
  rcases (motivicGeneratingMaps_iff R f).1 hf with (he | hn) | ha
  · rcases he with ⟨_⟩
    exact isIso_toAffineLineHomotopyCategory_map_emptyDescentMap R
  · rcases hn with ⟨Q⟩
    exact isIso_toAffineLineHomotopyCategory_map_nisnevichSquareMap R Q
  · rcases ha with ⟨U⟩
    exact isIso_toAffineLineHomotopyCategory_map_projection R U

end AlgebraicGeometry.MotivicHomotopy

attribute [colib_tag "COL-0391"]
  AlgebraicGeometry.MotivicHomotopy.isIso_fiberAtPoint_emptyDescentMap
  AlgebraicGeometry.MotivicHomotopy.motivicGeneratingMaps_isInvertedBy_toAffineLineHomotopyCategory
