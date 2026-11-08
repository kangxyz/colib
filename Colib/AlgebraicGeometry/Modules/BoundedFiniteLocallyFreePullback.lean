/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFiniteLocallyFreeWaldhausen
public import Colib.AlgebraicGeometry.Scheme.VectorBundle.Pullback
public import Colib.AlgebraicGeometry.Scheme.VectorBundle.KernelClosed
public import Colib.Algebra.Homology.CochainComplex.Cycles
public import StacksFrontier.Homology.KFlat.Bifunctor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Arbitrary pullback of actual bounded finite locally free complexes

The object predicate is native `boundedFiniteLocallyFreeComplex`: globally bounded terms
that are locally finite free. It is not the narrower global finite-free-retract predicate.
Quasi-isomorphisms are preserved because the actual cycles of an acyclic bounded complex
are finite locally free. Their short exact sequences remain exact after arbitrary pullback.
No exactness of the ambient module pullback, flatness of the morphism or resolution property
is assumed. This is a prerequisite for derived perfect localization naturality, not a
pullback on all locally perfect complexes.

Implementation provenance: `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Pullback.lean`
and `Quillen/AlgebraicGeometry/PerfectComplexes/Pullback.lean` at `c561118b`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory AlgebraicGeometry

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

variable {X Y Z : Scheme.{u}}

/-- Termwise native geometric pullback preserves global bounds and finite local freeness. -/
theorem boundedFiniteLocallyFreeComplex_pullback (f : X ⟶ Y)
    {K : CochainComplex Y.Modules ℤ} (hK : boundedFiniteLocallyFreeComplex Y K) :
    boundedFiniteLocallyFreeComplex X
      (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  obtain ⟨⟨a, b, hb⟩, ht⟩ := (boundedFiniteLocallyFreeComplex_iff_termBounds K).1 hK
  apply (boundedFiniteLocallyFreeComplex_iff_termBounds _).2
  exact ⟨⟨a, b, fun n hn => (Scheme.Modules.pullback f).map_isZero (hb n hn)⟩,
    fun n => SheafOfModules.IsFiniteLocallyFree.pullback_scheme f (K.X n) (ht n)⟩

/-- Actual acyclic bounded vector-bundle complexes stay acyclic under every pullback. -/
theorem acyclic_pullback_of_boundedFiniteLocallyFree (f : X ⟶ Y)
    {K : CochainComplex Y.Modules ℤ} (hK : boundedFiniteLocallyFreeComplex Y K)
    (ha : K.Acyclic) :
    (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  apply CochainComplex.acyclic_map_of_cycle_sequences
  intro n
  let : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (CochainComplex.cycleSequence K n).X₃ :=
    isFiniteLocallyFree_cycles_of_acyclic Y K hK ha (n + 1)
  exact Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree f
    (CochainComplex.cycleSequence K n)
    (CochainComplex.cycleSequence_shortExact K n (ha (n + 1)))

/-- The actual termwise pullback preserves quasi-isomorphisms between these complexes. -/
@[colib_tag "COL-0322",
  colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/Pullback.lean:55-84"
    "adaptation" "Native bounded finite locally free terms and actual cycle sequences; no flatness"]
theorem quasiIso_pullback_of_boundedFiniteLocallyFree (f : X ⟶ Y)
    {K L : CochainComplex Y.Modules ℤ} (hK : boundedFiniteLocallyFreeComplex Y K)
    (hL : boundedFiniteLocallyFreeComplex Y L) (s : K ⟶ L) [QuasiIso s] :
    QuasiIso (((Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map s) := by
  have hc := acyclic_pullback_of_boundedFiniteLocallyFree f
    (boundedFiniteLocallyFreeComplex_mappingCone hK hL s)
    ((CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone s).1 inferInstance)
  apply (CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone _).2
  intro n
  exact (hc n).of_iso
    (CochainComplex.mappingCone.mapHomologicalComplexIso s (Scheme.Modules.pullback f))

/-- Actual arbitrary geometric pullback on the full chain subcategory. -/
def boundedFiniteLocallyFreePullback (f : X ⟶ Y) :
    (boundedFiniteLocallyFreeComplex Y).FullSubcategory ⥤
      (boundedFiniteLocallyFreeComplex X).FullSubcategory :=
  (boundedFiniteLocallyFreeComplex X).lift
    ((boundedFiniteLocallyFreeComplex Y).ι ⋙
      (Scheme.Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ))
    (fun K => boundedFiniteLocallyFreeComplex_pullback f K.property)

instance boundedFiniteLocallyFreePullback_additive (f : X ⟶ Y) :
    (boundedFiniteLocallyFreePullback f).Additive := by
  dsimp [boundedFiniteLocallyFreePullback]
  infer_instance

/-- The original inherited conflations remain exact degree by degree. -/
def boundedFiniteLocallyFreeExactPullback (f : X ⟶ Y) :
    ExactFunctor (boundedFiniteLocallyFreeExactStructure Y)
      (boundedFiniteLocallyFreeExactStructure X) where
  toFunctor := boundedFiniteLocallyFreePullback f
  map_conflation S hS := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    let : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        ((S.map (boundedFiniteLocallyFreeComplex Y).ι).map
          (HomologicalComplex.eval Y.Modules (ComplexShape.up ℤ) n)).X₃ := S.X₃.property.2 n
    exact Scheme.Modules.shortExact_map_pullback_of_isFiniteLocallyFree f
      ((S.map (boundedFiniteLocallyFreeComplex Y).ι).map
        (HomologicalComplex.eval Y.Modules (ComplexShape.up ℤ) n))
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 hS n)

/-- Actual arbitrary pullback is exact for admissible cofibrations and quasi-isomorphisms. -/
@[colib_tag "COL-0322",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/Pullback.lean:54-67"
    "adaptation" "The actual native Waldhausen pullback with finite locally free quotients"]
theorem boundedFiniteLocallyFreePullback_isExact (f : X ⟶ Y) :
    Waldhausen.IsExact (boundedFiniteLocallyFreeWaldhausen Y).cof
      (boundedFiniteLocallyFreeWaldhausen Y).weq
      (boundedFiniteLocallyFreeWaldhausen X).cof
      (boundedFiniteLocallyFreeWaldhausen X).weq (boundedFiniteLocallyFreePullback f) where
  zero h := (boundedFiniteLocallyFreePullback f).map_isZero h
  cofibration s hs := (boundedFiniteLocallyFreeExactPullback f).map_inflation s hs
  weak {K L} s hs := by
    let : QuasiIso s.hom := hs
    exact quasiIso_pullback_of_boundedFiniteLocallyFree f K.property L.property s.hom
  pushout hi h := (boundedFiniteLocallyFreeExactPullback f).map_isPushout hi h

end Stacks.Perfect.BoundedLocallyFreeComplexes
