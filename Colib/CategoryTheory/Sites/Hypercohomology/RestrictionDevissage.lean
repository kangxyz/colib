/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Hypercohomology.SheafComparison
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Triangulated.Yoneda
import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations

/-!
# Restriction on bounded representable hypercohomology

Fix a morphism of the site. Its map between free representing sheaves induces
restriction by precomposition. The cone of the opposite map in the opposite
derived category identifies the complexes on which restriction is invertible
in every degree with the homological kernel of an additive Hom functor.

A bounded object belongs to that kernel when all its cohomology sheaves,
placed in degree zero, do. In nonnegative degrees the single-sheaf restriction
is the ordinary Ext restriction. Negative degrees vanish by orthogonality for
the canonical t-structure.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated Opposite

universe w w' t v u

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- For a fixed site arrow, the objects with invertible restriction in every
degree form a triangulated property, identified by the cone of the opposite
map on the actual free representing sheaves. -/
theorem exists_triangulated_derivedHomPresheaf_map {X Y : C} (f : X ⟶ Y) :
    ∃ P : ObjectProperty (DerivedCategory (Sheaf J AddCommGrpCat.{max v t})),
      P.IsTriangulated ∧ P.IsClosedUnderIsomorphisms ∧ ∀ E, P E ↔ ∀ p : ℤ,
        IsIso (((derivedHomPresheafFunctor.{w, t} J p).obj E).map f.op) := by
  let s := (DerivedCategory.singleFunctor _ 0).map ((freeYoneda.{t} J).map f)
  obtain ⟨W, g, δ, hT⟩ := CategoryTheory.Pretriangulated.distinguished_cocone_triangle s.op
  let T := Triangle.mk s.op g δ
  let P := (preadditiveCoyoneda.obj W).homologicalKernel
  refine ⟨P, inferInstance, inferInstance, fun E ↦ ?_⟩
  let F := preadditiveYoneda.obj E
  have h₁ := F.homologicalKernel.trW_iff_of_distinguished T hT
  have h₂ := F.mem_homologicalKernel_trW_iff s.op
  exact (F.mem_homologicalKernel_iff W).symm.trans (h₁.symm.trans h₂)

/-- A mapping cone has invertible hypercohomology restriction if restriction
is invertible in all degrees for both of its inputs. -/
theorem isIso_hypercohomologyPresheaf_map_mappingCone {X Y : C} (f : X ⟶ Y)
    {K L : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ} (g : K ⟶ L)
    (hK : ∀ p : ℤ, IsIso ((hypercohomologyPresheaf.{w, t} J K p).map f.op))
    (hL : ∀ p : ℤ, IsIso ((hypercohomologyPresheaf.{w, t} J L p).map f.op)) (p : ℤ) :
    IsIso ((hypercohomologyPresheaf.{w, t} J (CochainComplex.mappingCone g) p).map f.op) := by
  obtain ⟨P, hP, hClosed, hIso⟩ := exists_triangulated_derivedHomPresheaf_map.{w, t} J f
  have : P.IsTriangulated := hP
  have : P.IsClosedUnderIsomorphisms := hClosed
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle g)
  have hT : T ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished g
  have h₁ : P T.obj₁ := (hIso _).mpr hK
  have h₂ : P T.obj₂ := (hIso _).mpr hL
  exact (hIso _).mp (P.ext_of_isTriangulatedClosed₃ T hT h₁ h₂) p

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{max v t})]

private theorem isIso_derivedHomPresheaf_map_single
    {X Y : C} (f : X ⟶ Y) (F : Sheaf J AddCommGrpCat.{max v t})
    (h : ∀ n : ℕ, IsIso ((cohomologyPresheaf.{w', t} F n).map f.op)) (p : ℤ) :
    IsIso (((derivedHomPresheafFunctor.{w, t} J p).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).map f.op) := by
  by_cases hp : 0 ≤ p
  · let n := p.toNat
    have hn : (n : ℤ) = p := Int.toNat_of_nonneg hp
    rw [← hn]
    let H := hypercohomologyPresheaf.{w, t} J ((CochainComplex.singleFunctor _ 0).obj F) n
    let G := cohomologyPresheaf.{w', t} F n
    let eX : H.obj (op X) ≃+ G.obj (op X) := singleHypercohomologyEquivCohomology J F n X
    let eY : H.obj (op Y) ≃+ G.obj (op Y) := singleHypercohomologyEquivCohomology J F n Y
    have hcomm (z : H.obj (op Y)) : eX (H.map f.op z) = G.map f.op (eY z) :=
      singleHypercohomologyEquivCohomology_restriction J F n f z
    have hG : Function.Bijective (G.map f.op) :=
      (ConcreteCategory.isIso_iff_bijective _).mp (h n)
    change IsIso (H.map f.op)
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    constructor
    · intro x y hxy
      apply eY.injective
      apply hG.injective
      rw [← hcomm x, ← hcomm y, hxy]
    · intro x
      obtain ⟨y, hy⟩ := hG.surjective (eX x)
      refine ⟨eY.symm y, eX.injective ?_⟩
      rw [hcomm, eY.apply_symm_apply, hy]
  · let E := (DerivedCategory.singleFunctor _ 0).obj F
    let : (E⟦p⟧).IsGE (-p) := DerivedCategory.TStructure.t.isGE_shift E 0 p (-p) (by omega)
    have hZero (Z : C) : Subsingleton
        ((DerivedCategory.singleFunctor _ 0).obj ((freeYoneda.{t} J).obj Z) ⟶ E⟦p⟧) := by
      refine subsingleton_of_forall_eq 0 fun z ↦ ?_
      exact DerivedCategory.TStructure.t.zero z 0 (-p) (by omega)
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    constructor
    · intro _ _ _
      exact (hZero Y).elim _ _
    · intro z
      exact ⟨0, (hZero X).elim _ _⟩

/-- On a bounded derived object, restriction is invertible if it is invertible
on the ordinary cohomology of every cohomology sheaf in the interval. -/
theorem isIso_derivedHomPresheaf_map_of_bounded
    {X Y : C} (f : X ⟶ Y) (E : DerivedCategory (Sheaf J AddCommGrpCat.{max v t}))
    (a : ℤ) (n : ℕ) (hGE : E.IsGE a) (hLE : E.IsLE (a + (n : ℤ)))
    (h : ∀ (q : ℤ), a ≤ q → q ≤ a + (n : ℤ) → ∀ m : ℕ,
      IsIso ((cohomologyPresheaf.{w', t}
        ((DerivedCategory.homologyFunctor _ q).obj E) m).map f.op)) (p : ℤ) :
    IsIso (((derivedHomPresheafFunctor.{w, t} J p).obj E).map f.op) := by
  obtain ⟨P, hP, hClosed, hEquiv⟩ := exists_triangulated_derivedHomPresheaf_map.{w, t} J f
  have : P.IsTriangulated := hP
  have : P.IsClosedUnderIsomorphisms := hClosed
  have hE : P E := P.prop_of_isGE_of_isLE a n E hGE hLE (fun q hq₁ hq₂ ↦
    (hEquiv _).mpr (fun p ↦ isIso_derivedHomPresheaf_map_single J f _ (h q hq₁ hq₂) p))
  exact (hEquiv E).mp hE p

end Stacks.Cohomology.FreeYonedaUnivLE
