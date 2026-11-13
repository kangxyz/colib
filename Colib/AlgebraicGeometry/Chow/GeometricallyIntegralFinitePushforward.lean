/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatBaseChange
public import Colib.AlgebraicGeometry.Chow.GeometricallyIntegralPullback

/-!
# Finite pushforward after geometrically integral base change

A signed point in its own grade pulls back to the native inverse-image
generic with the same coefficient. Stacks 02RG gives the resulting
ungraded point equality for finite pushforward, retaining the original
residue degree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Function.locallyFinsuppWithin

universe u

attribute [local instance] Classical.propDecidable

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y X' Y' : Scheme.{u}}

/-- The actual finite pushforward of the lifted signed point is the lifted
image point with its original residue degree. -/
theorem finiteCyclePushforward_geometricallyIntegralPullbackPoint
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX']
    (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY']
    (f : X ⟶ Y) [IsFinite f]
    (g : Y' ⟶ Y) [LocallyOfFiniteType g] [Flat g] [GeometricallyIntegral g] [UniversallyOpen g]
    (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hsq : IsPullback g' f' f g)
    (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') (hg' : g' ≫ sX = sX')
    (r : ℕ) (hgr : AlgebraicGeometry.RelativeDimension g r)
    (x : X) (m : ℤ) :
    letI : IsFinite f' := MorphismProperty.of_isPullback hsq inferInstance
    letI : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    letI : GeometricallyIntegral g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    letI : UniversallyOpen g' := MorphismProperty.of_isPullback hsq.flip inferInstance
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    finiteCyclePushforward f' (single (geometricallyIntegralPullbackPoint g' x) m) =
      single (geometricallyIntegralPullbackPoint g (f x)) (m * (f.residueDegree x : ℤ)) := by
  let : IsFinite f' := MorphismProperty.of_isPullback hsq inferInstance
  let : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let : GeometricallyIntegral g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let : UniversallyOpen g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let d := relativeDimension C.dimensionFunction sX x
  let α := pointCycleAtOwnDimension C sX x m
  let β := properPushforward C sX sY f hf d α
  let hgr' := AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hgr
  have hd : d = relativeDimension C.dimensionFunction sY (f x) := by
    dsimp only [d]
    rw [← hf]
    exact relativeDimension_eq_of_finite_residueField C.dimensionFunction sY f x
      (residueField_finite_of_locallyQuasiFinite f x)
  have hβ : β.val = single (f x) (m * (f.residueDegree x : ℤ)) := by
    calc
      β.val = finiteCyclePushforward f α.val :=
        properPushforward_val_eq_finiteCyclePushforward C sX sY f hf d α
      _ = _ := finiteCyclePushforward_single f x m
  have hpoint (j : ℤ) (hj : j = relativeDimension C.dimensionFunction sY (f x))
      (γ : CycleGroup C sY j)
      (hγ : γ.val = single (f x) (m * (f.residueDegree x : ℤ))) :
      (flatPullback C sY' sY g hg r hgr j γ).val =
        single (geometricallyIntegralPullbackPoint g (f x)) (m * (f.residueDegree x : ℤ)) := by
    subst j
    have he : γ = pointCycleAtOwnDimension C sY (f x) (m * (f.residueDegree x : ℤ)) :=
      Subtype.ext hγ
    rw [he, flatPullback_pointCycleAtOwnDimension]
  calc
    _ = finiteCyclePushforward f' (flatPullback C sX' sX g' hg' r hgr' d α).val :=
      congrArg (finiteCyclePushforward f')
        (flatPullback_pointCycleAtOwnDimension C sX' sX g' hg' r hgr' x m).symm
    _ = (flatPullback C sY' sY g hg r hgr d β).val :=
      finiteCyclePushforward_flatPullback C sX sY sX' sY' f g g' f' hsq hf hg hg' r hgr d α
    _ = _ := hpoint d hd β hβ

end Stacks.Chow
