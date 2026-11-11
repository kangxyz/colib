/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSections
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectGlobalUnit
public import Colib.CategoryTheory.Functor.IdentityAutomorphismNaturality
public import Colib.CategoryTheory.Functor.IdentityAutomorphismEvaluation

/-!
# Scalar units on all-scheme bounded-above-flat sections

The identity automorphism is lifted through the original evaluation equivalence. Its
reindexing law follows from the genuine evaluation transition and geometric pullback of
scalars, without any assumption that the schemes are affine.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionUnit.lean`,
lines 34–64, at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.GrothendieckSections CategoryTheory.Functor.IdentityAutomorphism
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original geometric scalar lifted through original identity evaluation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionUnit.lean:35-39"
  "adaptation" "The same geometric scalar lifted through native global evaluation"]
def boundedAboveFlatGlobalSectionUnit (X : Scheme.{u}ᵒᵖ) (r : (Γ(X.unop, ⊤))ˣ) :
    𝟭 (BoundedAboveFlatGlobalSections X) ≅ 𝟭 (BoundedAboveFlatGlobalSections X) :=
  lift (boundedAboveFlatGlobalSectionEvaluation X)
    (boundedAboveFlatPerfectGlobalUnitIso X.unop r)

/-- Evaluation keeps every original scalar component literally. -/
theorem boundedAboveFlatGlobalSectionUnit_evaluation (X : Scheme.{u}ᵒᵖ) (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (boundedAboveFlatGlobalSectionEvaluation X)
      (boundedAboveFlatGlobalSectionUnit X r) (boundedAboveFlatPerfectGlobalUnitIso X.unop r) :=
  map_lift_hom (boundedAboveFlatGlobalSectionEvaluation X)
    (boundedAboveFlatPerfectGlobalUnitIso X.unop r)

/-- Original scheme reindexing preserves the actual pulled-back scalar unit. -/
theorem boundedAboveFlatGlobalSectionUnit_reindex {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y)
    (r : (Γ(X.unop, ⊤))ˣ) :
    Preserves (boundedAboveFlatGlobalSectionModelFunctor.map f).hom.toFunctor
      (boundedAboveFlatGlobalSectionUnit X r)
      (boundedAboveFlatGlobalSectionUnit Y (Units.map f.unop.appTop.hom.toMonoidHom r)) := by
  let e := (originalEvaluationTransitionIso boundedAboveFlatPerfectPseudofunctor X
    (Under.mk f)) ≪≫
    eqToIso (originalEvaluation_reindex boundedAboveFlatPerfectPseudofunctor X f).symm
  intro S
  apply (boundedAboveFlatGlobalSectionEvaluation Y).map_injective
  have h := map_hom_eq_of_iso _ _ e.symm (boundedAboveFlatGlobalSectionUnit X r)
    (boundedAboveFlatPerfectGlobalUnitIso Y.unop
      (Units.map f.unop.appTop.hom.toMonoidHom r)) (fun T => by
        change (boundedAboveFlatPerfectPullback f.unop).map
          ((boundedAboveFlatGlobalSectionEvaluation X).map
            ((boundedAboveFlatGlobalSectionUnit X r).hom.app T)) = _
        rw [boundedAboveFlatGlobalSectionUnit_evaluation,
          boundedAboveFlatPerfectPullback_map_globalUnit]
        rfl) S
  exact h.trans (boundedAboveFlatGlobalSectionUnit_evaluation Y _
    ((boundedAboveFlatGlobalSectionModelFunctor.map f).hom.toFunctor.obj S)).symm

/-- Equality with the actual pulled-back scalar gives the same reindexing action. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionLaurentScalar.lean:22-27"
  "adaptation" "The original arbitrary-scheme scalar equality specialization"]
theorem boundedAboveFlatGlobalSectionUnit_reindex_of_eq {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y)
    (r : (Γ(X.unop, ⊤))ˣ) (s : (Γ(Y.unop, ⊤))ˣ)
    (h : Units.map f.unop.appTop.hom.toMonoidHom r = s) :
    Preserves (boundedAboveFlatGlobalSectionsMap f)
      (boundedAboveFlatGlobalSectionUnit X r) (boundedAboveFlatGlobalSectionUnit Y s) := by
  subst s
  exact boundedAboveFlatGlobalSectionUnit_reindex f r

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0533"] boundedAboveFlatGlobalSectionUnit
attribute [colib_tag "COL-0533"] boundedAboveFlatGlobalSectionUnit_reindex_of_eq

end AlgebraicGeometry.Scheme.Modules
