/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteOpenRestriction
public import Colib.AlgebraicGeometry.Chow.PrincipalSection.Naturality
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.RelativeDivisor

/-!
# Principal cuts under an isomorphism of their original support

The actual support isomorphism restricts to an isomorphism of the whole
zero schemes, preserving their original inclusions and projections. The
finite pushforward therefore carries all original fundamental-cycle
coefficients under this transport.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow TopologicalSpace
open AlgebraicGeometry.Scheme AffineLineFiber

universe u

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k] {P D : Scheme.{u}}
  (e : D ≅ P) (b : P ⟶ Spec (.of k)) (b' : D ⟶ Spec (.of k)) (s : Γ(P, ⊤))

/-- The induced isomorphism on the actual zero fibers, with their full scheme structures. -/
def sectionCutFiberIso (hb : b' = e.hom ≫ b) :
    fiber (sectionToAffineLine b' (e.hom.appTop s)) 0 ≅ fiber (sectionToAffineLine b s) 0 := by
  let f := sectionToAffineLine b s
  have h : sectionToAffineLine b' (e.hom.appTop s) = e.hom ≫ f := by
    rw [hb, sectionToAffineLine_comp]
  letI : IsIso (AffineLineFiber.fiberMap f 0 e.hom) :=
    MorphismProperty.of_isPullback (AffineLineFiber.fiberMap_isPullback f 0 e.hom).flip
      inferInstance
  exact eqToIso (congrArg (fun t => fiber t 0) h) ≪≫ asIso (AffineLineFiber.fiberMap f 0 e.hom)

private theorem fiber_transport_inclusion {f g : D ⟶ Spec (.of (Polynomial k))} (h : f = g) :
    eqToHom (congrArg (fun t => fiber t 0) h) ≫ inclusion g 0 = inclusion f 0 := by
  subst g
  simp

/-- The whole fiber comparison preserves the literal original cut inclusion. -/
@[reassoc]
theorem sectionCutFiberIso_hom_inclusion (hb : b' = e.hom ≫ b) :
    (sectionCutFiberIso e b b' s hb).hom ≫ inclusion (sectionToAffineLine b s) 0 =
      inclusion (sectionToAffineLine b' (e.hom.appTop s)) 0 ≫ e.hom := by
  have h : sectionToAffineLine b' (e.hom.appTop s) = e.hom ≫ sectionToAffineLine b s := by
    rw [hb, sectionToAffineLine_comp]
  dsimp only [sectionCutFiberIso, Iso.trans_hom, eqToIso.hom, asIso_hom]
  rw [Category.assoc, AffineLineFiber.fiberMap_inclusion, ← Category.assoc,
    fiber_transport_inclusion h]

variable {X Y : SmoothSite (Spec (.of k))} (p : P ⟶ X.left) (g : P ⟶ Y.left)
  (h : p ≫ X.hom = g ≫ Y.hom)

set_option quotPrecheck false in
local notation "b₀" => (p ≫ X.hom)
set_option quotPrecheck false in
local notation "b₁" => ((e.hom ≫ p) ≫ X.hom)
set_option quotPrecheck false in
local notation "s₁" => e.hom.appTop s
set_option quotPrecheck false in
local notation "Z₀" => fiber (sectionToAffineLine b₀ s) (0 : k)
set_option quotPrecheck false in
local notation "Z₁" => fiber (sectionToAffineLine b₁ s₁) (0 : k)
set_option quotPrecheck false in
local notation "i₀" => inclusion (sectionToAffineLine b₀ s) (0 : k)
set_option quotPrecheck false in
local notation "i₁" => inclusion (sectionToAffineLine b₁ s₁) (0 : k)
set_option quotPrecheck false in
local notation "e₀" => sectionCutFiberIso e b₀ b₁ s (Category.assoc _ _ _)

private theorem sectionCutFiberIso_hom_projection :
    (e₀).hom ≫ i₀ ≫ p = i₁ ≫ e.hom ≫ p := by
  rw [sectionCutFiberIso_hom_inclusion_assoc]

/-- Finiteness of the original source projection is invariant under transport of a cut. -/
theorem isFinite_sectionCut_supportIso_iff : IsFinite (i₁ ≫ e.hom ≫ p) ↔ IsFinite (i₀ ≫ p) := by
  rw [← sectionCutFiberIso_hom_projection e s p]
  exact MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) _ _

/-- The original generic-image property is invariant under the actual cut isomorphism. -/
theorem sectionCut_generic_supportIso_iff :
    (∀ a : genericPoints Z₁, (i₁ ≫ e.hom ≫ p) a.val ∈ genericPoints X.left) ↔
      ∀ a : genericPoints Z₀, (i₀ ≫ p) a.val ∈ genericPoints X.left := by
  have he := sectionCutFiberIso_hom_projection e s p
  have hi : (e₀).inv ≫ i₁ ≫ e.hom ≫ p = i₀ ≫ p := by
    rw [← he, Iso.inv_hom_id_assoc]
  constructor
  · intro hg a
    have ha := hg ⟨(e₀).inv a.val, mem_genericPoints_of_flat (e₀).inv a.property⟩
    simpa only [← Scheme.Hom.comp_apply, hi] using ha
  · intro hg a
    have ha := hg ⟨(e₀).hom a.val, mem_genericPoints_of_flat (e₀).hom a.property⟩
    simpa only [← Scheme.Hom.comp_apply, he] using ha

/-- The whole principal cut correspondence is invariant under an isomorphism
of the support with its two original maps. -/
theorem sectionCutCorrespondence_supportIso
    [IsFinite (i₀ ≫ p)] [IsFinite (i₁ ≫ e.hom ≫ p)]
    (h₀ : ∀ a : genericPoints Z₀, (i₀ ≫ p) a.val ∈ genericPoints X.left)
    (h₁ : ∀ a : genericPoints Z₁, (i₁ ≫ e.hom ≫ p) a.val ∈ genericPoints X.left) :
    sectionCutCorrespondence (k := k) (X := X) (Y := Y) (P := D) (e.hom ≫ p) (e.hom ≫ g)
      (by simp only [Category.assoc, h]) s₁ h₁ =
        sectionCutCorrespondence (k := k) (X := X) (Y := Y) (P := P) p g h s h₀ := by
  let : IsNoetherian Z₀ := isNoetherian_of_finiteType (i₀ ≫ p)
  let : IsNoetherian Z₁ := isNoetherian_of_finiteType (e₀).hom
  let m := sectionCutSupportMap (k := k) (X := X) (Y := Y) (P := P) p g h s
  let m' := sectionCutSupportMap (k := k) (X := X) (Y := Y) (P := D) (e.hom ≫ p) (e.hom ≫ g)
    (by simp only [Category.assoc, h]) s₁
  have hm : (e₀).hom ≫ m = m' := by
    apply pullback.hom_ext
    · simp only [m, m', Category.assoc, sectionCutSupportMap_fst,
        sectionCutFiberIso_hom_inclusion_assoc]
    · simp only [m, m', Category.assoc, sectionCutSupportMap_snd,
        sectionCutFiberIso_hom_inclusion_assoc]
  apply Subtype.ext
  rw [sectionCutCorrespondence_val, sectionCutCorrespondence_val]
  change finiteCyclePushforward m' (AlgebraicCycle.fundamentalCycle Z₁) =
    finiteCyclePushforward m (AlgebraicCycle.fundamentalCycle Z₀)
  calc
    _ = finiteCyclePushforward ((e₀).hom ≫ m) (AlgebraicCycle.fundamentalCycle Z₁) :=
      finiteCyclePushforward_congr _ _ hm.symm _
    _ = _ := by
      rw [← finiteCyclePushforward_comp_apply, finiteCyclePushforward_fundamentalCycle_iso]

end AlgebraicGeometry.Cor
