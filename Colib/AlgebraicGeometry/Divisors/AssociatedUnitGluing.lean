/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# Gluing local unit multiples of one regular section

Local association units agree by cancellation of the same regular section.
Their glued section retains each of the specified local unit values.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

universe u v

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- Restriction to the actual open has the prescribed global sections comparison. -/
theorem opens_ι_appTop_eq_restriction (U : X.Opens) (s : Γ(X, ⊤)) :
    U.ι.appTop s = U.topIso.inv (X.presheaf.map (homOfLE le_top).op s) := by
  rw [U.ι_appTop]
  change X.presheaf.map (homOfLE _).op s =
    X.presheaf.map (eqToHom U.ι_image_top).op (X.presheaf.map (homOfLE le_top).op s)
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
  congr 2

/-- The actual global sections on any family of open immersions which covers
the scheme detect equality of global sections. -/
theorem globalSections_eq_of_openImmersion_cover {ι : Type v}
    {A : ι → Scheme.{u}} (f : ∀ i, A i ⟶ X) [∀ i, IsOpenImmersion (f i)]
    (h : ∀ x : X, ∃ i, x ∈ Set.range (f i)) {a b : Γ(X, ⊤)}
    (heq : ∀ i, (f i).appTop a = (f i).appTop b) : a = b := by
  let U (i : ι) := (f i).opensRange
  have hU : (⊤ : X.Opens) ≤ iSup U := fun x _ ↦ Opens.mem_iSup.2 (h x)
  apply X.sheaf.eq_of_locally_eq' U ⊤ (fun _ ↦ homOfLE le_top) hU
  intro i
  change X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op a =
    X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op b
  apply (ConcreteCategory.bijective_of_isIso (U i).topIso.inv).injective
  rw [← opens_ι_appTop_eq_restriction, ← opens_ι_appTop_eq_restriction]
  let e := (f i).isoOpensRange
  let : IsIso e.hom.appTop := by
    change IsIso (Scheme.Γ.map e.hom.op)
    infer_instance
  apply (ConcreteCategory.bijective_of_isIso e.hom.appTop).injective
  have hE : e.hom ≫ (U i).ι = f i := Hom.isoOpensRange_hom_ι _
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Hom.comp_appTop, hE]
  exact heq i

private theorem restrictSections_comp {U V W : X.Opens} (hUV : U ≤ V) (hVW : V ≤ W)
    (s : Γ(X, W)) :
    X.presheaf.map (homOfLE hUV).op (X.presheaf.map (homOfLE hVW).op s) =
      X.presheaf.map (homOfLE (hUV.trans hVW)).op s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- On an actual cover, association to one section whose restrictions are
regular gives one global unit with the same local values. -/
theorem exists_glued_associationUnit {ι : Type v} (V : ι → X.Opens) (U : X.Opens)
    (hVU : ∀ i, V i ≤ U) (hCover : U ≤ iSup V)
    (a b : Γ(X, U)) (μ : ∀ i, Γ(X, V i)ˣ)
    (hreg : ∀ i j, IsRightRegular
      (X.presheaf.map (homOfLE ((inf_le_left : V i ⊓ V j ≤ V i).trans (hVU i))).op a))
    (hμ : ∀ i, X.presheaf.map (homOfLE (hVU i)).op b =
      (μ i : Γ(X, V i)) * X.presheaf.map (homOfLE (hVU i)).op a) :
    ∃ u : Γ(X, U)ˣ, b = (u : Γ(X, U)) * a ∧
      ∀ i, X.presheaf.map (homOfLE (hVU i)).op (u : Γ(X, U)) = (μ i : Γ(X, V i)) := by
  have hU : U = iSup V := le_antisymm hCover (iSup_le hVU)
  subst U
  let s (i : ι) : Γ(X, V i) := μ i
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf V s := by
    intro i j
    let W := V i ⊓ V j
    let hi : W ≤ V i := inf_le_left
    let hj : W ≤ V j := inf_le_right
    let hW : W ≤ iSup V := hi.trans (le_iSup V i)
    change X.presheaf.map (homOfLE hi).op (μ i : Γ(X, V i)) =
      X.presheaf.map (homOfLE hj).op (μ j : Γ(X, V j))
    apply hreg i j
    have hlocal {k : ι} (hk : W ≤ V k) :
        X.presheaf.map (homOfLE hW).op b =
          X.presheaf.map (homOfLE hk).op (μ k : Γ(X, V k)) *
            X.presheaf.map (homOfLE hW).op a := by
      have h := congrArg (fun r : Γ(X, V k) ↦ X.presheaf.map (homOfLE hk).op r) (hμ k)
      have he : homOfLE (hVU k) = homOfLE (le_iSup V k) := Subsingleton.elim _ _
      rw [he, map_mul, restrictSections_comp (X := X) hk (le_iSup V k) b,
        restrictSections_comp (X := X) hk (le_iSup V k) a] at h
      exact h
    exact (hlocal hi).symm.trans (hlocal hj)
  obtain ⟨u, hu, -⟩ : ∃! u : Γ(X, iSup V),
      ∀ i, X.presheaf.map (Opens.leSupr V i).op u = s i :=
    X.sheaf.existsUnique_gluing V s hcompat
  have hunit : IsUnit u := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    have h := (μ i).isUnit.map (X.presheaf.germ (V i) x hi).hom
    change IsUnit (X.presheaf.germ (V i) x hi (s i)) at h
    rw [← hu i] at h
    change IsUnit (X.presheaf.germ (V i) x hi
      (X.presheaf.map (Opens.leSupr V i).op u)) at h
    exact (X.presheaf.germ_res_apply (Opens.leSupr V i) x hi u) ▸ h
  obtain ⟨v, hv⟩ := hunit
  refine ⟨v, ?_, fun i ↦ ?_⟩
  · rw [hv]
    apply X.sheaf.eq_of_locally_eq' V (iSup V) (Opens.leSupr V) le_rfl
    intro i
    change X.presheaf.map (Opens.leSupr V i).op b =
      X.presheaf.map (Opens.leSupr V i).op (u * a)
    rw [map_mul, hu i]
    exact hμ i
  · rw [hv]
    exact hu i

/-- The actual chart association units glue as global units of the base. -/
theorem exists_associationUnit_of_appTop_cover {ι : Type v}
    (V : ι → X.Opens) (hCover : (⊤ : X.Opens) ≤ iSup V)
    (a b : Γ(X, ⊤)) (μ : ∀ i, Γ((V i).toScheme, ⊤)ˣ)
    (hreg : ∀ i j, IsRightRegular ((V i ⊓ V j : X.Opens).ι.appTop a))
    (hμ : ∀ i, (V i).ι.appTop b = (μ i : Γ((V i).toScheme, ⊤)) * (V i).ι.appTop a) :
    ∃ u : Γ(X, ⊤)ˣ, b = (u : Γ(X, ⊤)) * a ∧
      ∀ i, (V i).ι.appTop (u : Γ(X, ⊤)) = (μ i : Γ((V i).toScheme, ⊤)) := by
  let ν (i : ι) := Units.map (V i).topIso.hom.hom.toMonoidHom (μ i)
  have hreg' (i j : ι) : IsRightRegular
      (X.presheaf.map (homOfLE (le_top : (V i ⊓ V j : X.Opens) ≤ ⊤)).op a) := by
    intro x y h
    apply (ConcreteCategory.bijective_of_isIso (V i ⊓ V j : X.Opens).topIso.inv).injective
    apply hreg i j
    rw [opens_ι_appTop_eq_restriction]
    simpa only [map_mul] using
      congrArg (fun s ↦ (V i ⊓ V j : X.Opens).topIso.inv s) h
  have hν (i : ι) : X.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op b =
      (ν i : Γ(X, V i)) * X.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op a := by
    have h := congrArg (fun s ↦ (V i).topIso.hom s) (hμ i)
    rw [opens_ι_appTop_eq_restriction, opens_ι_appTop_eq_restriction,
      map_mul, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at h
    exact h
  obtain ⟨u, hu, hlocal⟩ :=
    exists_glued_associationUnit V ⊤ (fun _ ↦ le_top) hCover a b ν hreg' hν
  refine ⟨u, hu, fun i ↦ ?_⟩
  rw [opens_ι_appTop_eq_restriction, hlocal i]
  exact Iso.hom_inv_id_apply _ _

/-- A local unit value on a compatible boundary chart cover gives the actual
global boundary value. -/
theorem appTop_eq_one_of_compatible_cover {ι : Type v}
    {D : Scheme.{u}} {A : ι → Scheme.{u}} (d : D ⟶ X) (V : ι → X.Opens)
    (a : ∀ i, A i ⟶ D) [∀ i, IsOpenImmersion (a i)]
    (c : ∀ i, A i ⟶ (V i).toScheme)
    (hc : ∀ i, a i ≫ d = c i ≫ (V i).ι)
    (ha : ∀ x : D, ∃ i, x ∈ Set.range (a i))
    (s : Γ(X, ⊤)) (hs : ∀ i, (c i).appTop ((V i).ι.appTop s) = 1) :
    d.appTop s = 1 := by
  apply globalSections_eq_of_openImmersion_cover a ha
  intro i
  rw [← CommRingCat.comp_apply, ← Hom.comp_appTop, hc i,
    Hom.comp_appTop, CommRingCat.comp_apply, hs i, map_one]

end AlgebraicGeometry.Scheme
