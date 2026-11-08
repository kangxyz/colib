/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Simplex.OrdinaryChains
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Exactness of the actual ordinary singular-chain functor

The existing ordinary chain functor preserves every shape of limits and colimits
that exists in its coefficient category. The proof uses native joint reflection
by evaluation, first at a chain degree and then at a smooth-site object. The
resulting coefficient functor is literally evaluation at `U × Δⁿ`.

In particular, the existing additive functor preserves finite limits, finite
colimits and short exact sequences whenever the coefficient category has the
corresponding finite limits and colimits. No transferred action, new chain
carrier, sheafification, or homotopy-invariance assumption is introduced.

This is a pointwise consequence of the ordinary-presheaf construction in
MVW2006, Definition 2.14, printed p. 16. The native implementation ingredients are
`HomologicalComplex.preservesLimitsOfShape_of_eval` and its colimit analogue,
and joint reflection by the native functor-category evaluation functors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

universe u v w a b

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]
variable {A : Type v} [Category.{w} A] [Preadditive A]

instance singularChainsFunctor_preservesLimitsOfShape
    (J : Type a) [Category.{b} J] [HasLimitsOfShape J A] :
    PreservesLimitsOfShape J (singularChainsFunctor R (A := A)) := by
  apply HomologicalComplex.preservesLimitsOfShape_of_eval
  intro n
  apply preservesLimitsOfShape_of_evaluation
  intro U
  exact inferInstanceAs (PreservesLimitsOfShape J
    ((evaluation _ A).obj (op (SmoothSite.product U.unop (smoothSiteObj R n)))))

instance singularChainsFunctor_preservesColimitsOfShape
    (J : Type a) [Category.{b} J] [HasColimitsOfShape J A] :
    PreservesColimitsOfShape J (singularChainsFunctor R (A := A)) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  apply preservesColimitsOfShape_of_evaluation
  intro U
  exact inferInstanceAs (PreservesColimitsOfShape J
    ((evaluation _ A).obj (op (SmoothSite.product U.unop (smoothSiteObj R n)))))

instance singularChainsFunctor_preservesFiniteLimits [HasFiniteLimits A] :
    PreservesFiniteLimits (singularChainsFunctor R (A := A)) :=
  ⟨fun _ _ _ => inferInstance⟩

instance singularChainsFunctor_preservesFiniteColimits [HasFiniteColimits A] :
    PreservesFiniteColimits (singularChainsFunctor R (A := A)) :=
  ⟨fun _ _ _ => inferInstance⟩

variable [HasFiniteLimits A] [HasFiniteColimits A]

/-- The native singular-chain functor preserves kernels and cokernels. -/
theorem singularChainsFunctor_preservesHomology :
    (singularChainsFunctor R (A := A)).PreservesHomology := inferInstance

/-- An exact sequence of ordinary presheaves gives an exact sequence of their chains. -/
@[colib_ref "MVW2006" "Lecture 2, Definition 2.14, p. 16, ordinary-presheaf clause"
  "generalization" "Pointwise exactness of ordinary singular chains over any base ring"]
theorem singularChainsFunctor_map_exact
    (S : ShortComplex ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)) (h : S.Exact) :
    (S.map (singularChainsFunctor R)).Exact := h.map _

/-- Short exact sequences retain their actual three induced chain maps. -/
theorem singularChainsFunctor_map_shortExact
    (S : ShortComplex ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)) (h : S.ShortExact) :
    (S.map (singularChainsFunctor R)).ShortExact := h.map_of_exact _

end AlgebraicSimplex
