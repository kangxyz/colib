/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.NormalComponents
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!
# Integral affine cover density and extension of ordinary sheaf maps

Actual integral affine opens cover every smooth separated finite-type scheme
over a field. The full inclusion is therefore cover dense for the actual
Nisnevich topology. Native dense-subsite gluing extends a natural map on this
subcategory into an ordinary sheaf, with restriction and uniqueness formulas.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Sheaves/IntegralAffineSheafIso.lean`
at motivic commit `a6805c4a87cdfd7717dd7a94039246a167f15380`. The geometric cover
retains the source's point-indexed nonempty affine members. Extension is stated
for arbitrary coefficient categories; in particular it applies without any
universe change to `AddCommGrpCat.{u + 1}`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v w

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (k : Type u) [Field k]

/-- A genuine affine open cover with a nonempty chosen member at every point. -/
def integralAffineCover (X : SmoothSite (Spec (.of k))) : X.left.OpenCover := by
  let C := (componentOpenCover k X).bind fun i =>
    ((componentOpenCover k X).X i).affineCover
  exact {
    I₀ := X.left
    X x := C.X (Scheme.Cover.idx C x)
    f x := C.f (Scheme.Cover.idx C x)
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x => ⟨x, Scheme.Cover.covers C x⟩, fun _ => inferInstance⟩ }

instance isAffine_integralAffineCover_obj (X : SmoothSite (Spec (.of k)))
    (i : (integralAffineCover k X).I₀) : IsAffine ((integralAffineCover k X).X i) := by
  dsimp [integralAffineCover]
  infer_instance

instance isIntegral_integralAffineCover_obj (X : SmoothSite (Spec (.of k)))
    (i : (integralAffineCover k X).I₀) : IsIntegral ((integralAffineCover k X).X i) := by
  let C := (componentOpenCover k X).bind fun j =>
    ((componentOpenCover k X).X j).affineCover
  have hn : Nonempty (C.X (Scheme.Cover.idx C i)) := by
    obtain ⟨x, _⟩ := Scheme.Cover.covers C i
    exact ⟨x⟩
  let : Nonempty (((componentOpenCover k X).X (Scheme.Cover.idx C i).1).affineCover.X
    (Scheme.Cover.idx C i).2) := hn
  change IsIntegral (((componentOpenCover k X).X (Scheme.Cover.idx C i).1).affineCover.X
    (Scheme.Cover.idx C i).2)
  apply isIntegral_of_isOpenImmersion
    (((componentOpenCover k X).X (Scheme.Cover.idx C i).1).affineCover.f (Scheme.Cover.idx C i).2)

/-- Integral affine arrows generate a genuine Nisnevich covering sieve. -/
theorem sieve_mem_of_integral_affine_arrows (X : SmoothSite (Spec (.of k))) (T : Sieve X)
    (h : ∀ (U : SmoothSite (Spec (.of k))) [IsAffine U.left] [IsIntegral U.left]
      (f : U ⟶ X), T f) : T ∈ nisnevichTopology (Spec (.of k)) X := by
  let C := integralAffineCover k X
  let U (i : C.I₀) : SmoothSite (Spec (.of k)) := mk (C.f i ≫ X.hom)
  let f (i : C.I₀) : U i ⟶ X := homMk (C.f i) rfl
  apply mem_nisnevichTopology_iff.mpr
  refine ⟨Presieve.ofArrows U f, ?_, ?_⟩
  · change (Presieve.ofArrows U f).map (forgetScheme _) ∈ Nisnevich.precoverage X.left
    rw [Presieve.map_ofArrows]
    exact Nisnevich.zariskiPrecoverage_le_precoverage _ C.mem₀
  · rw [Presieve.ofArrows_le_iff]
    intro i
    let : IsAffine (U i).left := by dsimp [U, C]; infer_instance
    let : IsIntegral (U i).left := by dsimp [U, C]; infer_instance
    exact h (U i) (f i)

/-- The property defining the genuine integral affine full subcategory. -/
def integralAffineProperty : ObjectProperty (SmoothSite (Spec (.of k))) :=
  fun X => IsAffine X.left ∧ IsIntegral X.left

/-- The full inclusion of the actual integral affine smooth schemes. -/
abbrev integralAffineInclusion := (integralAffineProperty k).ι

instance integralAffineInclusion_isCoverDense :
    (integralAffineInclusion k).IsCoverDense (nisnevichTopology (Spec (.of k))) where
  is_cover X := by
    apply sieve_mem_of_integral_affine_arrows k
    intro U _ _ f
    exact Presieve.in_coverByImage (integralAffineInclusion k)
      (Y := ⟨U, inferInstance, inferInstance⟩) f

section Coefficients

variable {A : Type v} [Category.{w} A]
  {F : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ A}
  {G : Sheaf (nisnevichTopology (Spec (.of k))) A}

/-- A natural map on integral affines extends into an ordinary sheaf by actual gluing. -/
def extendIntegralAffineHom
    (α : (integralAffineInclusion k).op ⋙ F ⟶
      (integralAffineInclusion k).op ⋙ G.obj) : F ⟶ G.obj :=
  Functor.IsCoverDense.sheafHom α

/-- Restricting the extension recovers the given map exactly. -/
@[simp] theorem extendIntegralAffineHom_restrict
    (α : (integralAffineInclusion k).op ⋙ F ⟶
      (integralAffineInclusion k).op ⋙ G.obj) :
    (integralAffineInclusion k).op.whiskerLeft (extendIntegralAffineHom k α) = α :=
  Functor.IsCoverDense.sheafHom_restrict_eq α

/-- A global ordinary map is recovered by extension of its restriction. -/
@[simp] theorem extendIntegralAffineHom_of_restrict (α : F ⟶ G.obj) :
    extendIntegralAffineHom k ((integralAffineInclusion k).op.whiskerLeft α) = α :=
  Functor.IsCoverDense.sheafHom_eq (integralAffineInclusion k) α

/-- Extension is the unique map with the prescribed integral affine restriction. -/
theorem extendIntegralAffineHom_unique
    (α : (integralAffineInclusion k).op ⋙ F ⟶
      (integralAffineInclusion k).op ⋙ G.obj) (β : F ⟶ G.obj)
    (hβ : (integralAffineInclusion k).op.whiskerLeft β = α) :
    β = extendIntegralAffineHom k α := by
  rw [← hβ, extendIntegralAffineHom_of_restrict]

/-- On an actual integral affine object, the extension has the prescribed component. -/
@[simp] theorem extendIntegralAffineHom_app
    (α : (integralAffineInclusion k).op ⋙ F ⟶
      (integralAffineInclusion k).op ⋙ G.obj)
    (X : (integralAffineProperty k).FullSubcategory) :
    (extendIntegralAffineHom k α).app (op X.obj) = α.app (op X) :=
  congr_app (extendIntegralAffineHom_restrict k α) (op X)

/-- Ordinary maps into a sheaf are detected by integral affine restriction. -/
theorem integralAffineHom_ext (α β : F ⟶ G.obj)
    (h : (integralAffineInclusion k).op.whiskerLeft α =
      (integralAffineInclusion k).op.whiskerLeft β) : α = β := by
  simpa only [extendIntegralAffineHom_of_restrict] using
    congrArg (extendIntegralAffineHom k) h

/-- The restriction/extension equivalence uses the actual native gluing map. -/
def integralAffineHomEquiv :
    ((integralAffineInclusion k).op ⋙ F ⟶ (integralAffineInclusion k).op ⋙ G.obj) ≃
      (F ⟶ G.obj) :=
  Functor.IsCoverDense.restrictHomEquivHom

/-- Isomorphisms of ordinary Nisnevich sheaves are detected on integral affine objects. -/
theorem isIso_of_integral_affine_app
    {F G : Sheaf (nisnevichTopology (Spec (.of k))) A} (φ : F ⟶ G)
    (h : ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left],
      IsIso (φ.hom.app (op X))) : IsIso φ := by
  apply Functor.IsCoverDense.iso_of_restrict_iso (G := integralAffineInclusion k) φ
  have : ∀ X : (integralAffineProperty k).FullSubcategoryᵒᵖ,
      IsIso (((integralAffineInclusion k).op.whiskerLeft φ.hom).app X) := by
    intro X
    have : IsAffine X.unop.obj.left := X.unop.property.1
    have : IsIntegral X.unop.obj.left := X.unop.property.2
    exact h X.unop.obj
  exact NatIso.isIso_of_isIso_app _

end Coefficients

end AlgebraicGeometry.Scheme.SmoothSite
