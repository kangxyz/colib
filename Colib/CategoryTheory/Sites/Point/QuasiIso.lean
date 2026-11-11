/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Quasi-isomorphisms of abelian sheaves at site points

The native fiber functor is exact, so its homology comparison identifies
the actual homology map at a point. A conservative family then reflects
each of these homology isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe w v u

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [LocallySmall.{w} C] [HasSheafify J AddCommGrpCat.{w}]

/-- The native fiber of abelian sheaves is additive. -/
instance sheafFiberAddCommGrpAdditive (Φ : J.Point.{w}) :
    (Φ.sheafFiber (A := AddCommGrpCat.{w})).Additive := by
  let F := Φ.sheafFiber (A := AddCommGrpCat.{w})
  let : HasBinaryProducts (Sheaf J AddCommGrpCat.{w}) :=
    (Abelian.hasFiniteLimits (C := Sheaf J AddCommGrpCat.{w})).out (Discrete WalkingPair)
  let : PreservesLimitsOfShape (Discrete WalkingPair) F :=
    (inferInstance : PreservesFiniteLimits F).preservesFiniteLimits _
  exact Functor.additive_of_preserves_binary_products F

/-- With enough points, quasi-isomorphisms of abelian sheaf complexes are
detected on the original fiber maps. -/
theorem quasiIso_iff_forall_sheafFiber [J.HasEnoughPoints.{w}]
    {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (Sheaf J AddCommGrpCat.{w}) c} (f : K ⟶ L) :
    QuasiIso f ↔ ∀ Φ : J.Point.{w},
      QuasiIso (((Φ.sheafFiber (A := AddCommGrpCat.{w})).mapHomologicalComplex c).map f) := by
  constructor
  · intro h Φ
    let : QuasiIso f := h
    infer_instance
  · intro h
    obtain ⟨P, _, hP⟩ := HasEnoughPoints.exists_objectProperty.{w} J
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff]
    let S := HomologicalComplex.shortComplexFunctor (Sheaf J AddCommGrpCat.{w}) c i
    let g := S.map f
    change IsIso (ShortComplex.homologyMap g)
    refine ((hP.jointlyReflectIsomorphisms AddCommGrpCat.{w}).isIso_iff _).2 (fun Φ => ?_)
    let F := Φ.obj.sheafFiber (A := AddCommGrpCat.{w})
    have hi := (quasiIso_iff _).1 (h Φ.obj) i
    rw [quasiIsoAt_iff, ShortComplex.quasiIso_iff] at hi
    let : IsIso (ShortComplex.homologyMap (F.mapShortComplex.map g)) := hi
    have hg : F.map (ShortComplex.homologyMap g) =
        ((S.obj K).mapHomologyIso F).inv ≫
          ShortComplex.homologyMap (F.mapShortComplex.map g) ≫
            ((S.obj L).mapHomologyIso F).hom := by
      rw [ShortComplex.mapHomologyIso_hom_naturality g F, Iso.inv_hom_id_assoc]
    change IsIso (F.map (ShortComplex.homologyMap g))
    rw [hg]
    infer_instance

end CategoryTheory.GrothendieckTopology.Point
