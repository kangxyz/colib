/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.GenericFiberLength
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Effective

/-!
# Native prime pullback along a geometrically integral flat morphism

The inverse image of the reduced closure of a point is integral. Its unique
native generic point has the dimension prescribed by Stacks 02R8. The actual
flat-pullback weight is one: restrict to the inverse image, identify the closed
fiber quotient by the actual stalk map, and evaluate its length at the generic
point of the reduced fiber. The comparison uses the native weight, including
its dimension filter, rather than a supplied multiplicity function.

Every original point is inserted in its own dimension grade. The conclusion
therefore does not require the original scheme to be integral or equidimensional.
The signed coefficient is an arbitrary integer.

Stacks implementation: 5ed82d14634e8d9576bb844c7bd4e3da66d450e7,
`Chow/RationalEquivalence/FlatPullbackPrincipalDivisor.lean:480-501` and
`Chow/RelativeCycles/Effective.lean:405-443`, under
`StacksFrontier/AlgebraicGeometry`. The closed-fiber length provider is the
separately supplied source-only `Scheme.GenericFiberLength` module.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

/-- A native point cycle placed in its own relative-dimension subgroup. -/
def pointCycleAtOwnDimension (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (x : X) (n : ℤ) :
    CycleGroup C sX (relativeDimension C.dimensionFunction sX x) :=
  ⟨single x n, by
    classical
    rw [mem_cyclesOfDimension_iff_forall_point]
    intro y hy
    have hyx : y = x := by
      by_contra hyx
      exact hy (by simp [single_apply, hyx])
    subst y
    rfl⟩

/-- At a whole-source generic point, the native weight is the true closed-fiber
length and is one when that fiber is reduced. No degree-one assertion is involved. -/
theorem flatPullbackWeight_eq_one_of_reduced_generic_fiber
    (C : ChowSituation.{u}) {P Q : Scheme.{u}}
    (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (f : P ⟶ Q)
    (η : genericPoints P) [IsReduced (f.fiber (f η.val))] :
    flatPullbackWeight C sP f (relativeDimension C.dimensionFunction sP η.val) η.val = 1 := by
  obtain ⟨ξ, hξ, _⟩ := exists_comap_genericPoint_over f (f η.val) η.val rfl
  have hs := specializes_iff_mem_closure.mpr hξ
  have he : ((integralComponentAt (f η.val)).comap f).subschemeι ξ.val = η.val :=
    (hs.antisymm (genericPoint_isMax η.val η.property hs)).eq
  rw [flatPullbackWeight_eq_length_quotient_extendedMaximalIdeal C sP f _ η.val
    ⟨ξ, he⟩ rfl, f.length_quotient_map_maximalIdeal_stalkMap η.val η.property]
  rfl

section IntegralInverseImage

variable {P Q : Scheme.{u}} (f : P ⟶ Q)
  [GeometricallyIntegral f] [Flat f] [UniversallyOpen f] [hQ : IsLocallyNoetherian Q]
  (x : Q)

/-- This is the full scheme-theoretic inverse image, before taking any reduction. -/
theorem isIntegral_comap_integralComponentAt :
    IsIntegral ((integralComponentAt x).comap f).subscheme := by
  let := isIntegral_integralComponentAt x
  let : IsLocallyNoetherian (integralComponentAt x).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (integralComponentAt x).subschemeι
  let : IsIntegral (pullback f (integralComponentAt x).subschemeι) := inferInstance
  exact IsIntegral.of_isIso ((integralComponentAt x).comapIso f).inv

/-- The unique generic of the actual inverse image, read in the original source. -/
def geometricallyIntegralPullbackPoint : P :=
  genericPointOf ((integralComponentAt x).comap f)
    (isIntegral_comap_integralComponentAt f x)

omit [Flat f] [UniversallyOpen f] [IsLocallyNoetherian Q] in
/-- The actual restricted map is geometrically integral, by its Cartesian square. -/
theorem geometricallyIntegral_comapRestrict_integralComponentAt :
    GeometricallyIntegral (comapRestrict (integralComponentAt x) f) :=
  MorphismProperty.of_isPullback
    (isPullback_comapRestrict (integralComponentAt x) f) inferInstance

/-- The unique inverse-image generic lies over the named original point. -/
@[simp]
theorem geometricallyIntegralPullbackPoint_map :
    f (geometricallyIntegralPullbackPoint f x) = x := by
  let W := integralComponentAt x
  let J := W.comap f
  let : IsIntegral W.subscheme := isIntegral_integralComponentAt x
  let : IsIntegral J.subscheme := isIntegral_comap_integralComponentAt f x
  let g := comapRestrict W f
  let : GeometricallyIntegral g := geometricallyIntegral_comapRestrict_integralComponentAt f x
  have hg : g (genericPoint J.subscheme) = genericPoint W.subscheme := by
    have hgen : IsGenericPoint (g (genericPoint J.subscheme)) (Set.univ : Set W.subscheme) := by
      have hrange : Set.range (fun a : J.subscheme => g a) = Set.univ :=
        Set.range_eq_univ.mpr g.surjective
      simpa only [Set.image_univ, hrange, closure_univ] using
        (genericPoint_spec J.subscheme).image g.continuous
    exact hgen.eq (genericPoint_spec W.subscheme)
  have hcomp := congrArg (fun a : J.subscheme ⟶ Q => a (genericPoint J.subscheme))
    (comapRestrict_subschemeι W f)
  calc
    f (geometricallyIntegralPullbackPoint f x) =
        W.subschemeι (g (genericPoint J.subscheme)) := hcomp.symm
    _ = x := by rw [hg]; exact genericPointOf_integralComponentAt x

end IntegralInverseImage

section NativePullback

variable (C : ChowSituation.{u}) {P Q : Scheme.{u}}
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
  (sQ : Q ⟶ C.S) [LocallyOfFiniteType sQ]
  (f : P ⟶ Q) [LocallyOfFiniteType f] [Flat f]
  [GeometricallyIntegral f] [UniversallyOpen f]
  (hbase : f ≫ sQ = sP) (r : ℕ) (hrel : AlgebraicGeometry.RelativeDimension f r)

include hbase hrel in
/-- The pointwise native dimension shift, without a pure-dimension premise on `Q`. -/
theorem relativeDimension_geometricallyIntegralPullbackPoint (x : Q) :
    relativeDimension C.dimensionFunction sP (geometricallyIntegralPullbackPoint
        (hQ := LocallyOfFiniteType.isLocallyNoetherian sQ) f x) =
      relativeDimension C.dimensionFunction sQ x + (r : ℤ) := by
  let : IsLocallyNoetherian Q := LocallyOfFiniteType.isLocallyNoetherian sQ
  let := isIntegral_comap_integralComponentAt f x
  exact relativeDimension_comap_genericPoint_eq_add C sQ sP f hbase r hrel x
    ⟨genericPoint ((integralComponentAt x).comap f).subscheme,
      genericPoint_mem_genericPoints ((integralComponentAt x).comap f).subscheme⟩

omit [LocallyOfFiniteType f] in
/-- The actual closed-fiber quotient at the inverse-image generic has length one.
The quotient is taken by the literal restricted stalk map, not by a chosen field map. -/
theorem length_comapRestrict_generic_fiber (x : Q) :
    letI := isIntegral_comap_integralComponentAt
      (hQ := LocallyOfFiniteType.isLocallyNoetherian sQ) f x
    let J := (integralComponentAt x).comap f
    let g := comapRestrict (integralComponentAt x) f
    let η := genericPoint J.subscheme
    Module.length (J.subscheme.presheaf.stalk η)
      ((J.subscheme.presheaf.stalk η) ⧸ Ideal.map (g.stalkMap η).hom
        (IsLocalRing.maximalIdeal
          ((integralComponentAt x).subscheme.presheaf.stalk (g η)))) = 1 := by
  let : IsLocallyNoetherian Q := LocallyOfFiniteType.isLocallyNoetherian sQ
  let := isIntegral_comap_integralComponentAt f x
  let := geometricallyIntegral_comapRestrict_integralComponentAt f x
  exact (comapRestrict (integralComponentAt x) f).length_quotient_map_maximalIdeal_stalkMap _
    (genericPoint_mem_genericPoints _)

include hbase hrel in
/-- Native 02RB at its exact original-point grade has coefficient one. The proof
passes through the actual closed fiber and native restriction-of-weight theorem. -/
@[stacks 02RB "geometrically integral inverse image; actual generic weight equals one"]
theorem flatPullbackWeight_geometricallyIntegralPullbackPoint (x : Q) :
    flatPullbackWeight C sP f
      (relativeDimension C.dimensionFunction sQ x + (r : ℤ))
      (geometricallyIntegralPullbackPoint
        (hQ := LocallyOfFiniteType.isLocallyNoetherian sQ) f x) = 1 := by
  let : IsLocallyNoetherian Q := LocallyOfFiniteType.isLocallyNoetherian sQ
  let J := (integralComponentAt x).comap f
  let : IsIntegral J.subscheme := isIntegral_comap_integralComponentAt f x
  let g := comapRestrict (integralComponentAt x) f
  let : GeometricallyIntegral g := geometricallyIntegral_comapRestrict_integralComponentAt f x
  rw [← relativeDimension_geometricallyIntegralPullbackPoint C sP sQ f hbase r hrel x]
  change flatPullbackWeight C sP f
    (relativeDimension C.dimensionFunction sP (J.subschemeι (genericPoint J.subscheme)))
    (J.subschemeι (genericPoint J.subscheme)) = 1
  rw [← flatPullbackWeight_comapRestrict,
    ← relativeDimension_comp_closedImmersion C.dimensionFunction J.subschemeι sP]
  exact flatPullbackWeight_eq_one_of_reduced_generic_fiber C (J.subschemeι ≫ sP) g
    ⟨genericPoint J.subscheme, genericPoint_mem_genericPoints _⟩

omit [LocallyOfFiniteType f] in
/-- Away from the unique generic, the native weight over this original point is zero. -/
theorem flatPullbackWeight_eq_zero_of_ne_geometricallyIntegralPullbackPoint
    (x : Q) (p : P) (hp : f p = x) (hpx : p ≠ geometricallyIntegralPullbackPoint
        (hQ := LocallyOfFiniteType.isLocallyNoetherian sQ) f x)
    (j : ℤ) : flatPullbackWeight C sP f j p = 0 := by
  let : IsLocallyNoetherian Q := LocallyOfFiniteType.isLocallyNoetherian sQ
  change closedSubschemeCycleCoeff C sP
    ((integralComponentAt (f p)).comap f).subschemeι j p = 0
  rw [hp]
  exact cycleAssociatedToClosedSubscheme_integral_apply_of_ne C sP
    ((integralComponentAt x).comap f) (isIntegral_comap_integralComponentAt f x) j hpx

/-- The actual native pullback of an arbitrary signed prime has the identical integer
coefficient at the unique inverse-image generic. No global grading is imposed. -/
@[stacks 02RB "native signed point cycle in its own dimension grade"]
theorem flatPullback_pointCycleAtOwnDimension (x : Q) (n : ℤ) :
    (flatPullback C sP sQ f hbase r hrel
      (relativeDimension C.dimensionFunction sQ x)
      (pointCycleAtOwnDimension C sQ x n)).val =
        single (geometricallyIntegralPullbackPoint
          (hQ := LocallyOfFiniteType.isLocallyNoetherian sQ) f x) n := by
  let : IsLocallyNoetherian Q := LocallyOfFiniteType.isLocallyNoetherian sQ
  classical
  apply Function.locallyFinsuppWithin.ext
  intro p
  rw [flatPullback_apply]
  change (single x n : AlgebraicCycle Q ℤ) (f p) * _ = _
  by_cases hp : p = geometricallyIntegralPullbackPoint f x
  · subst p
    rw [geometricallyIntegralPullbackPoint_map,
      flatPullbackWeight_geometricallyIntegralPullbackPoint C sP sQ f hbase r hrel]
    simp
  · by_cases hfx : f p = x
    · rw [flatPullbackWeight_eq_zero_of_ne_geometricallyIntegralPullbackPoint
        C sP sQ f x p hfx hp]
      simp [single_apply, hp]
    · simp [single_apply, hfx, hp]

end NativePullback

end Stacks.Chow
