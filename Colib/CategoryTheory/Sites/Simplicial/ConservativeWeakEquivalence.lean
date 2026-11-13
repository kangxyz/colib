/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.FiberStrictLift
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseWeakEquivalence
public import Colib.Topology.HELP.StrictFiniteCriterion
public import Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# A conservative family detects stalkwise weak equivalences

For each strict finite cube square, the arrows on which it admits a strict
lift up to relative homotopy form a sieve. The finite neighborhood descent
of the square and of the lift lets a conservative family detect the
original stalkwise realization weak equivalences.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Topology
open scoped Simplicial Topology

universe w v u

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C]
  {J : GrothendieckTopology C} {P Q : Cᵒᵖ ⥤ SSet.{w}} (f : P ⟶ Q)

private theorem realization_naturality {U V : C} (q : V ⟶ U) :
    (SSet.toTop.map (Q.map q.op)).hom.comp (SSet.toTop.map (f.app (op U))).hom =
      (SSet.toTop.map (f.app (op V))).hom.comp (SSet.toTop.map (P.map q.op)).hom := by
  rw [← TopCat.hom_comp, ← TopCat.hom_comp, ← Functor.map_comp, ← Functor.map_comp,
    f.naturality]

private theorem realization_fiber_naturality (Φ : J.Point.{w}) {U : C} (x : Φ.fiber.obj U) :
    (SSet.toTop.map (Φ.toPresheafFiber U x Q)).hom.comp (SSet.toTop.map (f.app (op U))).hom =
      (SSet.toTop.map (Φ.presheafFiber.map f)).hom.comp
        (SSet.toTop.map (Φ.toPresheafFiber U x P)).hom := by
  rw [← TopCat.hom_comp, ← TopCat.hom_comp, ← Functor.map_comp, ← Functor.map_comp,
    Φ.toPresheafFiber_naturality]

private theorem realization_fiber_restriction (Φ : J.Point.{w}) (T : Cᵒᵖ ⥤ SSet.{w})
    {U V : C} (q : V ⟶ U) (y : Φ.fiber.obj V) :
    (SSet.toTop.map (Φ.toPresheafFiber V y T)).hom.comp (SSet.toTop.map (T.map q.op)).hom =
      (SSet.toTop.map (Φ.toPresheafFiber U (Φ.fiber.map q y) T)).hom := by
  rw [← TopCat.hom_comp, ← Functor.map_comp, Φ.toPresheafFiber_w]

private def strictLiftSieve {U : C} {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (i : C(A, B)) (a : C(A, |P.obj (op U)|)) (b : C(B, |Q.obj (op U)|)) : Sieve U where
  arrows V q := StrictHomotopyLift (SSet.toTop.map (f.app (op V))).hom i
    ((SSet.toTop.map (P.map q.op)).hom.comp a) ((SSet.toTop.map (Q.map q.op)).hom.comp b)
  downward_closed := by
    intro V W q h r
    have e := StrictHomotopyLift.map h (SSet.toTop.map (P.map r.op)).hom
      (SSet.toTop.map (Q.map r.op)).hom (realization_naturality f r)
    simpa only [op_comp, Functor.map_comp, TopCat.hom_comp, ContinuousMap.comp_assoc] using e

variable [LocallySmall.{w} C]

private theorem sieve_mem_of_jointly_lifts
    {F : ObjectProperty (J.Point.{w})} [ObjectProperty.Small.{w} F]
    (hF : F.IsConservativeFamilyOfPoints)
    [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    {U : C} (R : Sieve U)
    (h : ∀ (ψ : F.FullSubcategory) (x : ψ.obj.fiber.obj U),
      ∃ (V : C) (q : V ⟶ U) (_ : R q) (y : ψ.obj.fiber.obj V), ψ.obj.fiber.map q y = x) :
    R ∈ J U := by
  rw [← R.ofArrows_category, hF.jointly_reflect_ofArrows_mem_of_small]
  intro ψ x
  obtain ⟨V, q, hq, y, hy⟩ := h ψ x
  exact ⟨⟨Over.mk q, hq⟩, y, hy⟩

/-- A small conservative family of points detects weakness at every actual
site fiber, using the same realization map in each case. -/
theorem isRealizationWeakEquivalence_presheafFiber_of_conservativeFamily
    {F : ObjectProperty (J.Point.{w})} [ObjectProperty.Small.{w} F]
    (hF : F.IsConservativeFamilyOfPoints)
    [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    (h : ∀ ψ : F.FullSubcategory, SSet.IsRealizationWeakEquivalence (ψ.obj.presheafFiber.map f))
    (Φ : J.Point.{w}) : SSet.IsRealizationWeakEquivalence (Φ.presheafFiber.map f) := by
  change IsWeakHomotopyEquivalence (SSet.toTop.map (Φ.presheafFiber.map f)).hom
  apply FiniteCubeStrictHELP.isWeakHomotopyEquivalence
  intro n a b w
  let i := CubicalTests.boundaryInclusion.{w} n
  let : CompactSpace (CubicalTests.boundaryPresentation.{w} n).space :=
    (CubicalTests.boundaryPresentation n).compact
  let : CompactSpace (CubicalTests.boundary.{w} n) :=
    (CubicalTests.boundaryPresentationHomeomorph n).compactSpace
  obtain ⟨U, x, a₀, b₀, ha₀, hb₀, w₀⟩ := Φ.exists_strictSquare_toPresheafFiber f i.hom a b w
  let R := strictLiftSieve f i.hom a₀ b₀
  have hR : R ∈ J U := sieve_mem_of_jointly_lifts hF R (by
    intro ψ y
    let p := (SSet.toTop.map (ψ.obj.toPresheafFiber U y P)).hom
    let q := (SSet.toTop.map (ψ.obj.toPresheafFiber U y Q)).hom
    have e : (SSet.toTop.map (ψ.obj.presheafFiber.map f)).hom.comp (p.comp a₀) =
        (q.comp b₀).comp i.hom := by
      rw [← ContinuousMap.comp_assoc, ← realization_fiber_naturality f ψ.obj y,
        ContinuousMap.comp_assoc, w₀, ContinuousMap.comp_assoc]
    have hψ : IsWeakHomotopyEquivalence (SSet.toTop.map (ψ.obj.presheafFiber.map f)).hom := h ψ
    obtain ⟨V, r, z, hr, hLift⟩ := ψ.obj.exists_refinement_of_strictLift_toPresheafFiber
      f y i.hom a₀ b₀ (hψ.cube_strictHELP n _ _ e)
    exact ⟨V, r, hLift, z, hr⟩)
  obtain ⟨V, r, hr, z, hz⟩ := Φ.jointly_surjective R hR x
  have hl : StrictHomotopyLift (SSet.toTop.map (f.app (op V))).hom i.hom
      ((SSet.toTop.map (P.map r.op)).hom.comp a₀)
      ((SSet.toTop.map (Q.map r.op)).hom.comp b₀) := hr
  have hLift := hl.map (SSet.toTop.map (Φ.toPresheafFiber V z P)).hom
    (SSet.toTop.map (Φ.toPresheafFiber V z Q)).hom (realization_fiber_naturality f Φ z)
  change StrictHomotopyLift (SSet.toTop.map (Φ.presheafFiber.map f)).hom i.hom a b
  rw [← ha₀, ← hb₀]
  simpa only [← ContinuousMap.comp_assoc, realization_fiber_restriction, hz] using hLift

end CategoryTheory.GrothendieckTopology.Point

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] {J : GrothendieckTopology C}

/-- The existing pointed stalkwise localization may test any small
conservative family of the actual site points. -/
theorem stalkwiseWeakEquivalences_iff_conservativeFamily
    {F : ObjectProperty (J.Point.{w})} [ObjectProperty.Small.{w} F]
    (hF : F.IsConservativeFamilyOfPoints)
    [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    {P Q : PointedSimplicialPresheaf.{w} C} (f : P ⟶ Q) :
    stalkwiseWeakEquivalences C J f ↔
      ∀ ψ : F.FullSubcategory, SSet.IsRealizationWeakEquivalence ((fiberAtPoint C ψ.obj).map f) :=
  ⟨fun h ψ => h ψ.obj, fun h =>
    GrothendieckTopology.Point.isRealizationWeakEquivalence_presheafFiber_of_conservativeFamily
      f.right hF h⟩

end CategoryTheory.PointedSimplicialPresheaf
