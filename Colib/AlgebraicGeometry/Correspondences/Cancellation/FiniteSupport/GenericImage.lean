/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.CutDominance
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.FiniteSupport.Component
import Colib.AlgebraicGeometry.Chow.PrincipalSection.Zero
import Colib.AlgebraicGeometry.Sites.Smooth.NormalComponents

/-!
# Generic images of finite section cuts on a torus component support

The original finite support factors through the native torus over its open
source component. A finite cut is nonzero and every generic point of its
whole zero scheme maps to a generic point of the original base.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Stacks.Chow TopologicalSpace

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X P : Scheme.{u}} [IsIntegral P] [IsNoetherian P]
  (f : X ⟶ Spec (.of k)) [Smooth f] [IsLocallyNoetherian X] [IsNormal X]
  (g : P ⟶ pullback f (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k)))
  [IsFinite g]

set_option quotPrecheck false in
local notation "q" => (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k))
set_option quotPrecheck false in
local notation "p" => (g ≫ pullback.fst f q)
set_option quotPrecheck false in
local notation "b" => (p ≫ f)
set_option quotPrecheck false in
local notation "Z₀(" s ")" => AffineLineFiber.fiber (sectionToAffineLine b s) (0 : k)
set_option quotPrecheck false in
local notation "i₀(" s ")" => AffineLineFiber.inclusion (sectionToAffineLine b s) (0 : k)

/-- A whole finite cut on the original support of a torus component has
nonzero equation and only generic images over the original base. -/
theorem sectionCut_nonzero_and_generic_of_finite_torus_component
    (hrange : Set.range g ∈ irreducibleComponents (pullback f q : Scheme)) :
    ∀ (s : Γ(P, ⊤)), IsFinite (i₀(s) ≫ p) →
      s ≠ 0 ∧ ∀ a : genericPoints Z₀(s), (i₀(s) ≫ p) a.val ∈ genericPoints X := by
  obtain ⟨U, g₀, hgfin, hgsurj, hg⟩ := exists_finite_surjective_torus_component f g hrange
  let C := pullback (U.ι ≫ f) q
  let π := pullback.fst (U.ι ≫ f) q
  let r := π ≫ U.ι
  let c : C ⟶ Spec (.of k) := r ≫ f
  let : IsSeparated q := inferInstanceAs (IsSeparated
    (SmoothSite.multiplicativeGroupObject (Spec (.of k))).hom)
  let : SmoothOfRelativeDimension 1 r :=
    inferInstanceAs (SmoothOfRelativeDimension (1 + 0) (π ≫ U.ι))
  let : Smooth r := SmoothOfRelativeDimension.smooth 1 r
  let : Smooth c := inferInstanceAs (Smooth (r ≫ f))
  let : IsSeparated r := inferInstanceAs (IsSeparated (π ≫ U.ι))
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of k)) c
  let : IsNormal C := isNormal_of_isRegular C (isRegular_of_smooth_over_field c)
  let : IrreducibleSpace C := Function.Surjective.irreducibleSpace g₀.continuous g₀.surjective
  let : IsIntegral C := isIntegral_of_irreducibleSpace_of_isReduced C
  have hproj : pullbackParameterExtensionMap U.ι f q ≫ pullback.fst f q = r :=
    pullbackParameterExtensionMap_fst U.ι f q
  have hp : g₀ ≫ r = p := by
    rw [← hproj, ← Category.assoc, hg]
  have hnonfinite : ¬ IsFinite p := by
    intro h
    let : IsFinite ((g₀ ≫ π) ≫ U.ι) := by
      rw [Category.assoc]
      exact hp.symm ▸ h
    let : IsFinite (g₀ ≫ π) := IsFinite.of_comp (g₀ ≫ π) U.ι
    exact not_isFinite_support_projection (U.ι ≫ f) g₀ (π (g₀ (genericPoint P))) inferInstance
  intro s hs
  have hne : s ≠ 0 := section_ne_zero_of_isFinite_zero b p s hs hnonfinite
  refine ⟨hne, fun a => ?_⟩
  have hi : i₀(s) ≫ g₀ ≫ r = i₀(s) ≫ p := congrArg (fun m => i₀(s) ≫ m) hp
  let : IsFinite (i₀(s) ≫ g₀ ≫ r) := hi.symm ▸ hs
  have h := section_zero_image_mem_genericPoints_of_finite_dominant g₀ r b s hne a
  exact (congrArg (fun m => m a.val) hi) ▸ h

end AlgebraicGeometry.NativeTorusPolynomial
