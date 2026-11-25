/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCutOpenEvaluation
public import Colib.Topology.Realization.CompactFamilyContinuity
public import Colib.Topology.Realization.DoubleCylinderSimplexCoverage

/-!
# Joint continuity of compact families on the actual two-tip reference carrier

Each original characteristic simplex factors through one of the original summands
of each simplicial double cylinder. On a cylinder the actual realization isomorphism
retains the nerve and interval coordinates. This gives continuity against the entire
native input on each characteristic simplex, and finite support then gives joint
continuity along every compact map into the unchanged carrier, in every native level.
No continuity on the unrestricted carrier product is claimed.

Adapted from `CommonReferenceNerveCutOpenCompactFamily.lean` in Quillen K-theory at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory TopCat
open scoped Simplicial Topology unitInterval
universe u v

namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenCarrier
open SmallWaldhausenCategory SSet

variable {V W T : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (J : W ⟶ T)
  (G : V ⟶ T) (ε₀ ε₁ : G.hom.toFunctor ≅ (F ≫ J).hom.toFunctor)

private theorem realizedCylinder_hom_apply {X Y Z : SSet.{u}}
    (f : X ⟶ Y) (g : X ⟶ Z) (x : |X ⊗ Δ[1]|) :
    DoubleCylinder.realizedCylinder f g ((realizationCylinderIso X).hom x) =
      SSet.toTop.map (DoubleCylinder.simplicialCylinder f g) x := by
  have h : (realizationCylinderIso X).hom ≫ DoubleCylinder.realizedCylinder f g =
      SSet.toTop.map (DoubleCylinder.simplicialCylinder f g) := by
    simp [DoubleCylinder.realizedCylinder]
  exact ConcreteCategory.congr_hom h x

private theorem nativeEval_firstCylinder_compact_continuous
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (q : C(S, |parameterSSet F ⊗ Δ[1]|)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦
      nativeEval F J G ε₀ ε₁ n
        (SSet.toTop.map (left₁ F J G ε₀ ε₁)
          (SSet.toTop.map (DoubleCylinder.simplicialCylinder
            (attaching F J G ε₀) (erase F)) (q z.1))) z.2) := by
  let r : C(S, |parameterSSet F| × TopCat.I) :=
    (realizationCylinderIso (parameterSSet F)).hom.hom.comp q
  let p : C(S, |parameterSSet F|) :=
    ⟨fun s ↦ (r s).1, continuous_fst.comp r.continuous⟩
  let c : C(S, I) :=
    ⟨fun s ↦ (r s).2.down, continuous_uliftDown.comp (continuous_snd.comp r.continuous)⟩
  apply (nativeEval_cylinderMinus_compact_continuous F J G ε₀ ε₁ p c n).congr
  intro z
  apply congrArg (fun y ↦ nativeEval F J G ε₀ ε₁ n y z.2)
  change SSet.toTop.map (left₁ F J G ε₀ ε₁)
      (DoubleCylinder.realizedCylinder (attaching F J G ε₀) (erase F)
        ((realizationCylinderIso (parameterSSet F)).hom (q z.1))) = _
  exact congrArg (SSet.toTop.map (left₁ F J G ε₀ ε₁))
    (realizedCylinder_hom_apply (attaching F J G ε₀) (erase F) (q z.1))

private theorem nativeEval_secondCylinder_compact_continuous
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (q : C(S, |parameterSSet F ⊗ Δ[1]|)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦
      nativeEval F J G ε₀ ε₁ n
        (SSet.toTop.map (DoubleCylinder.simplicialCylinder
          (secondAttaching F J G ε₀ ε₁) (erase F)) (q z.1)) z.2) := by
  let r : C(S, |parameterSSet F| × TopCat.I) :=
    (realizationCylinderIso (parameterSSet F)).hom.hom.comp q
  let p : C(S, |parameterSSet F|) :=
    ⟨fun s ↦ (r s).1, continuous_fst.comp r.continuous⟩
  let c : C(S, I) :=
    ⟨fun s ↦ (r s).2.down, continuous_uliftDown.comp (continuous_snd.comp r.continuous)⟩
  apply (nativeEval_cylinderPlus_compact_continuous F J G ε₀ ε₁ p c n).congr
  intro z
  apply congrArg (fun y ↦ nativeEval F J G ε₀ ε₁ n y z.2)
  change DoubleCylinder.realizedCylinder (secondAttaching F J G ε₀ ε₁) (erase F)
      ((realizationCylinderIso (parameterSSet F)).hom (q z.1)) = _
  exact realizedCylinder_hom_apply (secondAttaching F J G ε₀ ε₁) (erase F) (q z.1)

private theorem nativeEval_first_simplex_continuous (n k : ℕ)
    (simplexMap : (Δ[k] : SSet.{u}) ⟶ firstSimplicial F J G ε₀) :
    Continuous (fun z : |(Δ[k] : SSet.{u})| × (prespectrum V).space n ↦
      nativeEval F J G ε₀ ε₁ n
        (SSet.toTop.map (left₁ F J G ε₀ ε₁) (SSet.toTop.map simplexMap z.1)) z.2) := by
  rcases DoubleCylinder.characteristicSimplex_factors
      (attaching F J G ε₀) (erase F) ⦋k⦌ simplexMap with
    ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩
  · rw [← hq, Functor.map_comp]
    exact nativeEval_firstCylinder_compact_continuous F J G ε₀ ε₁
      (SSet.toTop.map q).hom n
  · have hq' : q ≫ left₀ F J G ε₀ = simplexMap := hq
    rw [← hq', Functor.map_comp]
    change Continuous (fun z : |(Δ[k] : SSet.{u})| × (prespectrum V).space n ↦
      nativeEval F J G ε₀ ε₁ n
        (laurentInclusion F J G ε₀ ε₁ (SSet.toTop.map q z.1)) z.2)
    exact nativeEval_laurent_compact_continuous F J G ε₀ ε₁ (SSet.toTop.map q).hom n
  · have hq' : q ≫ right₀ F J G ε₀ = simplexMap := hq
    rw [← hq', Functor.map_comp]
    refine (continuous_const : Continuous
      (fun _ : |(Δ[k] : SSet.{u})| × (prespectrum V).space n ↦
        (nativeCone J).point n)).congr ?_
    intro z
    change (nativeCone J).point n = nativeEval F J G ε₀ ε₁ n
      (SSet.toTop.map (left₁ F J G ε₀ ε₁)
        (SSet.toTop.map (right₀ F J G ε₀) (SSet.toTop.map q z.1))) z.2
    have ht : SSet.toTop.map q z.1 = (default : |tipSSet.{u}|) := Subsingleton.elim _ _
    rw [ht]
    exact (nativeEval_tipMinus F J G ε₀ ε₁ n z.2).symm

/-- Every actual characteristic simplex has joint continuity with the whole native input. -/
theorem nativeEval_simplex_continuous (n k : ℕ)
    (simplexMap : (Δ[k] : SSet.{u}) ⟶ simplicial F J G ε₀ ε₁) :
    Continuous (fun z : |(Δ[k] : SSet.{u})| × (prespectrum V).space n ↦
      nativeEval F J G ε₀ ε₁ n (SSet.toTop.map simplexMap z.1) z.2) := by
  rcases DoubleCylinder.characteristicSimplex_factors
      (secondAttaching F J G ε₀ ε₁) (erase F) ⦋k⦌ simplexMap with
    ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨q, hq⟩
  · rw [← hq, Functor.map_comp]
    exact nativeEval_secondCylinder_compact_continuous F J G ε₀ ε₁
      (SSet.toTop.map q).hom n
  · have hq' : q ≫ left₁ F J G ε₀ ε₁ = simplexMap := hq
    rw [← hq', Functor.map_comp]
    exact nativeEval_first_simplex_continuous F J G ε₀ ε₁ n k q
  · have hq' : q ≫ right₁ F J G ε₀ ε₁ = simplexMap := hq
    rw [← hq', Functor.map_comp]
    refine (continuous_const : Continuous
      (fun _ : |(Δ[k] : SSet.{u})| × (prespectrum V).space n ↦
        (nativeCone J).point n)).congr ?_
    intro z
    change (nativeCone J).point n = nativeEval F J G ε₀ ε₁ n
      (SSet.toTop.map (right₁ F J G ε₀ ε₁) (SSet.toTop.map q z.1)) z.2
    have ht : SSet.toTop.map q z.1 = (default : |tipSSet.{u}|) := Subsingleton.elim _ _
    rw [ht]
    exact (nativeEval_tipPlus F J G ε₀ ε₁ n z.2).symm

/-- Any compact map into the unchanged two-tip carrier gives genuine joint continuity.
The original native input is unrestricted, and the same parameter map works at every level. -/
theorem nativeEval_compact_continuous
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, space F J G ε₀ ε₁)) (n : ℕ) :
    Continuous (fun z : S × (prespectrum V).space n ↦
      nativeEval F J G ε₀ ε₁ n (p z.1) z.2) :=
  SSet.realization_compactFamily_continuous (simplicial F J G ε₀ ε₁)
    (fun z ↦ nativeEval F J G ε₀ ε₁ n z.1 z.2)
    (nativeEval_simplex_continuous F J G ε₀ ε₁ n) p

/-- The exact original evaluator packaged as a joint compact-parameter native family. -/
def compactNativeFamily
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, space F J G ε₀ ε₁)) (n : ℕ) :
    C(S × (prespectrum V).space n, (nativeCone J).space n) :=
  ⟨fun z ↦ nativeEval F J G ε₀ ε₁ n (p z.1) z.2,
    nativeEval_compact_continuous F J G ε₀ ε₁ p n⟩

/-- Packaging changes neither the carrier point nor the original native input. -/
theorem compactNativeFamily_apply
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, space F J G ε₀ ε₁)) (n : ℕ) (s : S) (x : (prespectrum V).space n) :
    compactNativeFamily F J G ε₀ ε₁ p n (s, x) =
      nativeEval F J G ε₀ ε₁ n (p s) x := rfl

/-- The same compact carrier parameter preserves the original point at every level. -/
theorem compactNativeFamily_point
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, space F J G ε₀ ε₁)) (n : ℕ) (s : S) :
    compactNativeFamily F J G ε₀ ε₁ p n (s, (prespectrum V).point n) =
      (nativeCone J).point n :=
  nativeEval_point F J G ε₀ ε₁ n (p s)

/-- Structure time remains independent of the compact carrier parameter at all levels. -/
theorem compactNativeFamily_structure
    {S : Type v} [TopologicalSpace S] [CompactSpace S]
    (p : C(S, space F J G ε₀ ε₁)) (n : ℕ) (s : S)
    (x : (prespectrum V).space n) (t : I) :
    compactNativeFamily F J G ε₀ ε₁ p (n + 1) (s, (prespectrum V).structureMap n x t) =
      (nativeCone J).structureMap n (compactNativeFamily F J G ε₀ ε₁ p n (s, x)) t :=
  nativeEval_structure F J G ε₀ ε₁ n (p s) x t

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenCarrier
