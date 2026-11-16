/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.BoundedBelowComparison
public import Colib.AlgebraicGeometry.KTheory.PerfectFlatPullback

/-! # Flat pullback of bounded below perfect complexes -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.Modules.BoundedBelowPerfect

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]

local notation "F" => (Functor.mapHomologicalComplex (pullback f) (ComplexShape.up ℤ))

/-- Actual flat pullback retains a strict lower term bound and native perfectness. -/
def flatPullback : Obj Y ⥤ Obj X :=
  ObjectProperty.lift (objects X) ((objects Y).ι ⋙ (F)) (fun K => by
    obtain ⟨a, ha⟩ := K.property.2
    let := ha
    refine ⟨Complex.isPerfectComplex_flatPullback f K.obj K.property.1, a,
      (CochainComplex.isStrictlyGE_iff _ _).mpr ?_⟩
    intro i hi
    exact (pullback f).map_isZero (K.obj.isZero_of_isStrictlyGE a i hi))

instance flatPullback_additive : (flatPullback f).Additive where
  map_add {K L g h} := by
    apply ObjectProperty.hom_ext
    exact (F).map_add (f := g.hom) (g := h.hom)

private theorem flatPullback_shortExact {S : ShortComplex (Obj Y)}
    (hS : (S.map (objects Y).ι).ShortExact) :
    ((S.map (flatPullback f)).map (objects X).ι).ShortExact := by
  let : PreservesFiniteLimits (pullback f) := pullback_preservesFiniteLimits_of_flat f
  exact hS.map_of_exact (F)

/-- The literal bounded below flat pullback is Waldhausen exact. -/
theorem flatPullback_exact :
    Waldhausen.IsExact (waldhausen Y).cof (waldhausen Y).weq (waldhausen X).cof (waldhausen X).weq
      (flatPullback f) := by
  let E : ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex Y.Modules ℤ))
        (objects Y))
      (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
        (objects X)) :=
    { toFunctor := flatPullback f
      map_conflation := fun _ hS => flatPullback_shortExact f hS }
  refine { zero := fun h => (flatPullback f).map_isZero h
           cofibration := fun g hg => E.map_inflation g hg
           weak := ?_
           pushout := fun hi hp => E.map_isPushout hi hp }
  intro K L g hg
  exact (perfectFlatPullback_waldhausenExact f).weak ((inclusion Y).map g) hg

/-- The two pullbacks agree on the literal inclusion. -/
def flatPullbackInclusionIso :
    flatPullback f ⋙ inclusion X ≅ inclusion Y ⋙ perfectFlatPullback f :=
  NatIso.ofComponents
    (fun _ => ObjectProperty.isoMk
      (P := RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) (Iso.refl _))
    (fun _ => by
      apply ObjectProperty.hom_ext
      simp
      rfl)

end AlgebraicGeometry.Scheme.Modules.BoundedBelowPerfect
