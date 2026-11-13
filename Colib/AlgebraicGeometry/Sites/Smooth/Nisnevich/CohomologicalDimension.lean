/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.CohomologySequence
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.StandardDensityRefinement
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen
import Colib.AlgebraicGeometry.Sites.Smooth.Injectives
import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteSections
import Colib.CategoryTheory.Sites.Cohomology.LocalTriviality

/-!
# Cohomological dimension from reducing Nisnevich squares

For the actual smooth Nisnevich cohomology presheaf, a class in degree `n`
vanishes after restriction along a map in standard density degree `n`.
The proof uses the covering zero-restriction sieve in positive degree,
simple refinements of that sieve, and the natural geometric boundary on
distinguished squares. In a square the first reduction kills the restrictions
to both pieces. The second reduction kills the boundary preimage on the overlap.

The two geometric inputs are completeness for simple refinements and reduction
for the chosen squares. Above the topological Krull dimension the resulting
open immersion is invertible, giving the projective dimension bound on the
native free representing sheaf.

See Voevodsky, [Homotopy theory of simplicial sheaves in completely
decomposable topologies](https://arxiv.org/abs/0805.4578), Theorem 2.27.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.FreeYonedaUnivLE

universe u w

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}}

private theorem restriction_comp_apply {G : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{w}}
    {X Y Z : SmoothSite S} (f : X ⟶ Y) (g : Y ⟶ Z) (x : G.obj (op Z)) :
    G.map (f ≫ g).op x = G.map f.op (G.map g.op x) := by
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

private theorem restriction_eq_zero_of_factorization
    {G : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{w}} {W V A B X : SmoothSite S}
    (f : W ⟶ V) (φ : V ⟶ X) (a : W ⟶ A) (j : A ⟶ B) (g : B ⟶ X)
    (h : f ≫ φ = a ≫ j ≫ g) (x : G.obj (op X))
    (hz : G.map j.op (G.map g.op x) = 0) :
    G.map f.op (G.map φ.op x) = 0 := by
  rw [← restriction_comp_apply, h, restriction_comp_apply, restriction_comp_apply, hz, map_zero]

section HasExt

variable [HasExt.{w} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})]

private theorem cohomology_eq_zero_of_empty
    (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) (n : ℕ)
    (X : SmoothSite S) (hX : IsEmpty X.left)
    (x : (cohomologyPresheaf.{w, u + 1} F n).obj (op X)) : x = 0 := by
  let : IsEmpty X.left := hX
  let P := (freeYoneda.{u + 1} (nisnevichTopology S)).obj X
  have hId : (𝟙 P) = 0 := by
    apply (sectionsAddEquiv.{u + 1} X P).injective
    exact (section_eq_zero_of_isEmpty P X _).trans (section_eq_zero_of_isEmpty P X _).symm
  let y : Ext.{w} P F n := x
  change y = 0
  exact (Ext.mk₀_id_comp y).symm.trans (by rw [hId, Ext.mk₀_zero, Ext.zero_comp])

private theorem exists_densityMap_restriction_eq_zero_of_simple
    (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
    {P : Square (SmoothSite S) → Prop}
    (hGeo : ∀ Q, P Q → IsGeometricNisnevichSquare Q) (hReduce : NisnevichSquaresReduce P)
    (n : ℕ) (hLower : ∀ (W : SmoothSite S)
      (y : (cohomologyPresheaf.{w, u + 1} F n).obj (op W)),
      ∃ (Y : SmoothSite S) (j : Y ⟶ W), IsStandardDensityMap j n ∧
        (cohomologyPresheaf.{w, u + 1} F n).map j.op y = 0)
    {X : SmoothSite S} {R : Sieve X} (hR : HasSimpleNisnevichRefinement P X R) :
    ∀ (x : (cohomologyPresheaf.{w, u + 1} F (n + 1)).obj (op X)),
      (∀ ⦃Y : SmoothSite S⦄ (f : Y ⟶ X), R f →
        (cohomologyPresheaf.{w, u + 1} F (n + 1)).map f.op x = 0) →
      ∃ (Y : SmoothSite S) (j : Y ⟶ X), IsStandardDensityMap j (n + 1) ∧
        (cohomologyPresheaf.{w, u + 1} F (n + 1)).map j.op x = 0 := by
  let H := cohomologyPresheaf.{w, u + 1} F (n + 1)
  let G := cohomologyPresheaf.{w, u + 1} F n
  induction hR with
  | identity h =>
    intro x hx
    exact ⟨_, 𝟙 _, IsStandardDensityMap.id _ _, hx _ h⟩
  | empty h =>
    intro x _
    exact ⟨_, 𝟙 _, IsStandardDensityMap.id _ _,
      cohomology_eq_zero_of_empty F (n + 1) _ h (H.map (𝟙 _).op x)⟩
  | @square Q hQ R h₂ h₃ ih₂ ih₃ =>
    intro x hx
    obtain ⟨A, j₂, hD₂, hz₂⟩ := ih₂ (H.map Q.f₂₄.op x) (by
      intro Y f hf
      rw [← restriction_comp_apply]
      exact hx (f ≫ Q.f₂₄) hf)
    obtain ⟨V, j₃, hD₃, hz₃⟩ := ih₃ (H.map Q.f₃₄.op x) (by
      intro Y f hf
      rw [← restriction_comp_apply]
      exact hx (f ≫ Q.f₃₄) hf)
    obtain ⟨Q', hQ', φ, hφ, _, ⟨a, ha⟩, ⟨v, hv⟩⟩ :=
      hReduce Q hQ n (𝟙 Q.X₁) j₂ j₃ (IsStandardDensityMap.id _ _) hD₂ hD₃
    let x' := H.map φ.τ₄.op x
    have hz₂' : H.map Q'.f₂₄.op x' = 0 :=
      restriction_eq_zero_of_factorization Q'.f₂₄ φ.τ₄ a j₂ Q.f₂₄
        (by rw [φ.comm₂₄, ← ha, Category.assoc]) x hz₂
    have hz₃' : H.map Q'.f₃₄.op x' = 0 :=
      restriction_eq_zero_of_factorization Q'.f₃₄ φ.τ₄ v j₃ Q.f₃₄
        (by rw [φ.comm₃₄, ← hv, Category.assoc]) x hz₃
    have hGeo' := hGeo Q' hQ'
    obtain ⟨Z', z', hClosed', hComp', hIso'⟩ := hGeo'.complement
    let : IsOpenImmersion Q'.f₂₄.left := hGeo'.isOpenImmersion
    let : Etale Q'.f₃₄.left := hGeo'.etale
    let : IsClosedImmersion z' := hClosed'
    let : IsIso (pullback.snd Q'.f₃₄.left z') := hIso'
    obtain ⟨y, hy⟩ := exists_nisnevichCohomologyBoundary_eq_of_restriction_zero
      Q' hGeo'.isPullback z' hComp' F n x' hz₂' hz₃'
    obtain ⟨B, j, hD, hz⟩ := hLower Q'.X₁ y
    obtain ⟨Q'', hQ'', ψ, hψ, ⟨b, hb⟩, _, _⟩ :=
      hReduce Q' hQ' n j (𝟙 Q'.X₂) (𝟙 Q'.X₃) hD
        (IsStandardDensityMap.id _ _) (IsStandardDensityMap.id _ _)
    have hz' : G.map ψ.τ₁.op y = 0 := by
      rw [← hb, restriction_comp_apply, hz, map_zero]
    have hGeo'' := hGeo Q'' hQ''
    obtain ⟨Z'', z'', hClosed'', hComp'', hIso''⟩ := hGeo''.complement
    let : IsOpenImmersion Q''.f₂₄.left := hGeo''.isOpenImmersion
    let : Etale Q''.f₃₄.left := hGeo''.etale
    let : IsClosedImmersion z'' := hClosed''
    let : IsIso (pullback.snd Q''.f₃₄.left z'') := hIso''
    have hn := ConcreteCategory.congr_hom
      (nisnevichCohomologyBoundary_naturality Q'' hGeo''.isPullback z'' hComp''
        Q' hGeo'.isPullback z' hComp' ψ F n) y
    change H.map ψ.τ₄.op (nisnevichCohomologyBoundary Q' hGeo'.isPullback z' hComp' F n y) =
      nisnevichCohomologyBoundary Q'' hGeo''.isPullback z'' hComp'' F n
        (G.map ψ.τ₁.op y) at hn
    have hZero : H.map ψ.τ₄.op x' = 0 := by
      rw [← hy, hn, hz', map_zero]
    refine ⟨Q''.X₄, ψ.τ₄ ≫ φ.τ₄, hψ.comp hφ, ?_⟩
    rw [restriction_comp_apply]
    exact hZero

variable [IsNoetherian S]

/-- The standard density degree of an open immersion needed to kill an
ordinary Nisnevich cohomology class is at most its cohomological degree. -/
theorem exists_densityMap_restriction_eq_zero
    {P : Square (SmoothSite S) → Prop}
    (hGeo : ∀ Q, P Q → IsGeometricNisnevichSquare Q)
    (hComplete : NisnevichSimpleRefinements P) (hReduce : NisnevichSquaresReduce P)
    (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) (n : ℕ) (X : SmoothSite S)
    (x : (cohomologyPresheaf.{w, u + 1} F n).obj (op X)) :
    ∃ (Y : SmoothSite S) (j : Y ⟶ X), IsStandardDensityMap j n ∧
      (cohomologyPresheaf.{w, u + 1} F n).map j.op x = 0 := by
  induction n generalizing X with
  | zero =>
    let U : X.left.Opens := ⊥
    let Y := (opensFunctor X).obj U
    let j : Y ⟶ X := openInclusion X U
    let hj : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion U.ι)
    let : IsOpenImmersion j.left := hj
    have hEmpty : IsEmpty Y.left := ⟨fun y ↦ by
      have hy : j.left y ∈ j.left.opensRange := Scheme.Hom.mem_opensRange.mpr ⟨y, rfl⟩
      change U.ι y ∈ U.ι.opensRange at hy
      rw [Scheme.Opens.opensRange_ι] at hy
      exact (show U.ι y ∉ U by simp [U]) hy⟩
    exact ⟨Y, j, ⟨hj, TopologicalSpace.Opens.isInStandardDensity_zero _⟩,
      cohomology_eq_zero_of_empty F 0 Y hEmpty ((cohomologyPresheaf F 0).map j.op x)⟩
  | succ n ih =>
    let H := cohomologyPresheaf.{w, u + 1} F (n + 1)
    let R := Presheaf.equalizerSieve (F := H) x 0
    have hR : R ∈ nisnevichTopology S X :=
      zeroSieve_mem_succ (nisnevichTopology S) F n X x
    refine exists_densityMap_restriction_eq_zero_of_simple F hGeo hReduce n ih
      (hComplete X R hR) x ?_
    intro Y f hf
    change H.map f.op x = H.map f.op 0 at hf
    simpa only [map_zero] using hf

/-- Ordinary smooth Nisnevich cohomology vanishes above the topological
Krull dimension when the chosen squares give complete reducing refinements. -/
theorem nisnevichCohomology_eq_zero_of_topologicalKrullDim_lt
    {P : Square (SmoothSite S) → Prop}
    (hGeo : ∀ Q, P Q → IsGeometricNisnevichSquare Q)
    (hComplete : NisnevichSimpleRefinements P) (hReduce : NisnevichSquaresReduce P)
    (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) (n : ℕ) (X : SmoothSite S)
    (hd : topologicalKrullDim X.left < n)
    (x : (cohomologyPresheaf.{w, u + 1} F n).obj (op X)) : x = 0 := by
  obtain ⟨Y, j, hj, hx⟩ := exists_densityMap_restriction_eq_zero hGeo hComplete hReduce F n X x
  let : IsIso j := hj.isIso_of_topologicalKrullDim_lt hd
  apply (AddCommGrpCat.mono_iff_injective ((cohomologyPresheaf.{w, u + 1} F n).map j.op)).mp
    inferInstance
  simpa only [map_zero] using hx

end HasExt

variable [IsNoetherian S]

/-- The geometric dimension bound gives the projective dimension of the
actual free abelian Nisnevich sheaf representing a smooth scheme. -/
theorem freeYoneda_hasProjectiveDimensionLE_of_topologicalKrullDim_le
    {P : Square (SmoothSite S) → Prop}
    (hGeo : ∀ Q, P Q → IsGeometricNisnevichSquare Q)
    (hComplete : NisnevichSimpleRefinements P) (hReduce : NisnevichSquaresReduce P)
    (X : SmoothSite S) (d : ℕ) (hd : topologicalKrullDim X.left ≤ d) :
    HasProjectiveDimensionLE ((freeYoneda.{u + 1} (nisnevichTopology S)).obj X) d := by
  let : HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) :=
    hasExt_of_enoughInjectives _
  refine HasProjectiveDimensionLT.mk ?_
  intro n hn F x
  have hn' : (d : WithBot ℕ∞) < n :=
    WithBot.coe_lt_coe.mpr (ENat.natCast_lt_natCast.mpr (Nat.lt_of_succ_le hn))
  exact nisnevichCohomology_eq_zero_of_topologicalKrullDim_lt
    hGeo hComplete hReduce F n X (hd.trans_lt hn') x

end AlgebraicGeometry.Scheme.SmoothSite
