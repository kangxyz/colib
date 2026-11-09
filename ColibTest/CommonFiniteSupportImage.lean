/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Basic
import Colib.AlgebraicGeometry.Morphisms.Finite.CommonImage
import Colib.AlgebraicGeometry.Morphisms.ClosedImmersion.BaseChange.ClosedImageBaseChange

/-!
# Consumers of the common finite support geometry

The first consumer uses the nonzero points of the actual native correspondence,
not a second cycle model. Its selected subschemes are the native
`integralComponentAt`, and their images are not reduced or replaced after target
postcomposition. The other consumers retain the entire support under arbitrary
base change and show that literal support factorizations remain literal there.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

section NativeCorrespondence

variable {S X Y V : Scheme.{u}}
  (x : X ⟶ S) (y : Y ⟶ S) (v : V ⟶ S) (q : V ⟶ Y) (hq : q ≫ y = v)

private noncomputable def postcomposeTarget : pullback x v ⟶ pullback x y :=
  pullback.lift (pullback.fst x v) (pullback.snd x v ≫ q) (by
    rw [Category.assoc, hq]
    exact pullback.condition)

example [IsSeparated y] [LocallyOfFiniteType y]
    (c : finiteCorrespondences x v) (hne : c.1.support.Nonempty) :
    ∃ (C : Scheme.{u}) (j : C ⟶ pullback x y),
      IsClosedImmersion j ∧ IsFinite (j ≫ pullback.fst x y) ∧
      ∀ (z : pullback (C := Scheme) x v), z ∈ c.1.support →
        ∃ r : (integralComponentAt z).subscheme ⟶ C,
        r ≫ j = (integralComponentAt z).subschemeι ≫ postcomposeTarget x y v q hq := by
  classical
  have hs : c.2.1.toFinset.Nonempty := by simpa using hne
  obtain ⟨C, j, hj, hfinite, hr⟩ := exists_finite_common_closed_image
    (fun z : pullback (C := Scheme) x v ↦ (integralComponentAt z).subscheme)
    (fun z ↦ (integralComponentAt z).subschemeι ≫ postcomposeTarget x y v q hq)
    (pullback.fst x y) c.2.1.toFinset hs (by
      intro z hz
      have hz' : c.1 z ≠ 0 := by simpa using hz
      simpa only [Category.assoc, postcomposeTarget, pullback.lift_fst]
        using (c.2.2 z hz').1)
  refine ⟨C, j, hj, hfinite, ?_⟩
  intro z hz
  exact hr z (by simpa using hz)

end NativeCorrespondence

section WholeSupportBaseChange

open ClosedImageBaseChange

variable {S X Y U C D : Scheme.{u}}
  (x : X ⟶ S) (y : Y ⟶ S) (u : U ⟶ S)
  (g : U ⟶ X) (hg : g ≫ x = u) (j : C ⟶ pullback x y)

example [IsClosedImmersion j] [IsFinite (j ≫ pullback.fst x y)] :
    IsClosedImmersion (inclusion x y u g hg j) ∧
      IsFinite (inclusion x y u g hg j ≫ pullback.fst u y) :=
  ⟨inferInstance, inferInstance⟩

/-- A factorization into the actual common support survives arbitrary source
base change, preserving both the support map and the source map. -/
example (a : D ⟶ pullback x y) (r : D ⟶ C) (hr : r ≫ j = a) :
    ∃ e : pullback (a ≫ pullback.fst x y) g ⟶
        pullback (j ≫ pullback.fst x y) g,
      e ≫ pullback.fst (j ≫ pullback.fst x y) g =
        pullback.fst (a ≫ pullback.fst x y) g ≫ r ∧
      e ≫ pullback.snd (j ≫ pullback.fst x y) g =
        pullback.snd (a ≫ pullback.fst x y) g ∧
      e ≫ inclusion x y u g hg j = inclusion x y u g hg a := by
  let e : pullback (a ≫ pullback.fst x y) g ⟶
      pullback (j ≫ pullback.fst x y) g :=
    pullback.lift (pullback.fst (a ≫ pullback.fst x y) g ≫ r)
      (pullback.snd (a ≫ pullback.fst x y) g) (by
        rw [Category.assoc, ← Category.assoc r j, hr]
        exact pullback.condition)
  refine ⟨e, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
  apply pullback.hom_ext
  · simp only [Category.assoc, inclusion_fst, e, pullback.lift_snd]
  · simp only [Category.assoc, inclusion_snd, e, pullback.lift_fst_assoc]
    rw [← Category.assoc r j, hr]

end WholeSupportBaseChange
