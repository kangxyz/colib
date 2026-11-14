/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.BaseChange
public import Colib.AlgebraicGeometry.Sites.Smooth.ForgetBase
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Change of base on the smooth Nisnevich site

For a scheme morphism, direct image evaluates a sheaf on the actual pullback.
For a smooth separated finite-type morphism, its left adjoint evaluates a
sheaf on the same scheme with the composite structure map. This is the
ordinary Nisnevich site adjunction underlying the relative-to-absolute passage
in Riou, *Opérations de Steenrod motiviques*, arXiv:1207.3121v1,
Proposition 1.4.2 and Definition 3.0.1.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S T : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The base change of an arrow lies in its Cartesian square of schemes. -/
theorem baseChange_map_isPullback (r : T ⟶ S) {X Y : SmoothSite S} (f : X ⟶ Y) :
    IsPullback ((baseChange r).map f).left (pullback.fst X.hom r)
      (pullback.fst Y.hom r) f.left := by
  apply IsPullback.of_right (h₁₂ := pullback.snd Y.hom r) (h₂₂ := Y.hom) (v₁₃ := r)
  · rw [baseChange_map_snd, MorphismProperty.Over.w]
    exact (baseChange_isPullback r X).flip
  · exact baseChange_map_fst r f
  · exact (baseChange_isPullback r Y).flip

instance (r : T ⟶ S) : (nisnevichPrecoverage S).PullbacksPreservedBy (baseChange r) where
  preservesPairwisePullbacks_of_mem {_ _} hR := by
    refine ⟨?_⟩
    intro X Y f g hf hg
    have : Etale f.left := etale_of_mem_nisnevichPrecoverage hR hf
    have : PreservesLimit (cospan f g) (baseChange r ⋙ forget T) :=
      preservesLimit_of_natIso _ (MorphismProperty.Over.pullbackCompForgetIso
        (P := smoothSeparatedFiniteType) (Q := ⊤) r).symm
    exact preservesLimit_of_reflects_of_preserves (baseChange r) (forget T)

instance (r : T ⟶ S) : (baseChange r).IsContinuous
    (nisnevichTopology S) (nisnevichTopology T) := by
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
  intro X R hR
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  change (Presieve.ofArrows Y f).map (baseChange r) ∈ nisnevichPrecoverage T _
  rw [Presieve.map_ofArrows, mem_nisnevichPrecoverage_iff, Presieve.map_ofArrows]
  apply Precoverage.mem_coverings_of_isPullback (fun i ↦ (f i).left)
    (by rwa [mem_nisnevichPrecoverage_iff, Presieve.map_ofArrows] at hR)
    (pullback.fst X.hom r) (fun i ↦ ((baseChange r).map (f i)).left)
    (fun i ↦ pullback.fst (Y i).hom r)
  exact fun i ↦ baseChange_map_isPullback r (f i)

variable (r : T ⟶ S) (A : Type*) [Category* A]

/-- Direct image along `r`, by restriction along the actual base-change functor. -/
def nisnevichDirectImage :
    Sheaf (nisnevichTopology T) A ⥤ Sheaf (nisnevichTopology S) A :=
  (baseChange r).sheafPushforwardContinuous A _ _

@[simp]
theorem nisnevichDirectImage_obj_obj (F : Sheaf (nisnevichTopology T) A)
    (X : SmoothSite S) :
    ((nisnevichDirectImage r A).obj F).obj.obj (.op X) =
      F.obj.obj (.op ((baseChange r).obj X)) := rfl

variable [Smooth r] [IsSeparated r] [QuasiCompact r]

instance : (nisnevichPrecoverage T).PullbacksPreservedBy (forgetBase r) where
  preservesPairwisePullbacks_of_mem {_ _} hR := by
    refine ⟨?_⟩
    intro X Y f g hf hg
    have : Etale f.left := etale_of_mem_nisnevichPrecoverage hR hf
    have : PreservesLimit (cospan f g) (forgetBase r ⋙ forgetScheme S) :=
      inferInstanceAs (PreservesLimit (cospan f g) (forgetScheme T))
    exact preservesLimit_of_reflects_of_preserves (forgetBase r) (forgetScheme S)

instance : (forgetBase r).IsContinuous (nisnevichTopology T) (nisnevichTopology S) := by
  apply Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy
  simp only [nisnevichPrecoverage, ← Precoverage.comap_comp]
  exact le_rfl

/-- Scheme postcomposition is left adjoint to the actual fiber-product functor. -/
def forgetBaseAdjunction : forgetBase r ⊣ baseChange r := by
  letI : smoothSeparatedFiniteType.{u}.IsStableUnderComposition :=
    @MorphismProperty.IsStableUnderComposition.inf Scheme.{u} _
      (@Smooth ⊓ @IsSeparated) @QuasiCompact
      (MorphismProperty.IsStableUnderComposition.inf (P := @Smooth) (Q := @IsSeparated))
      inferInstance
  let hr : smoothSeparatedFiniteType r := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  exact MorphismProperty.Over.mapPullbackAdj smoothSeparatedFiniteType ⊤ r hr trivial

/-- The unit is the graph of the original structure map into the fiber product. -/
@[simp]
theorem forgetBaseAdjunction_unit_app_left (X : SmoothSite T) :
    ((forgetBaseAdjunction r).unit.app X).left =
      pullback.lift (𝟙 X.left) X.hom (by simp) := rfl

/-- The counit is the projection from the fiber product onto the original scheme. -/
@[simp]
theorem forgetBaseAdjunction_counit_app_left (X : SmoothSite S) :
    ((forgetBaseAdjunction r).counit.app X).left = pullback.fst X.hom r := rfl

/-- Inverse image for a smooth separated finite-type base map is literal restriction. -/
def nisnevichInverseImage :
    Sheaf (nisnevichTopology S) A ⥤ Sheaf (nisnevichTopology T) A :=
  (forgetBase r).sheafPushforwardContinuous A _ _

@[simp]
theorem nisnevichInverseImage_obj_obj (F : Sheaf (nisnevichTopology S) A)
    (X : SmoothSite T) :
    ((nisnevichInverseImage r A).obj F).obj.obj (.op X) =
      F.obj.obj (.op ((forgetBase r).obj X)) := rfl

/-- Smooth inverse image is left adjoint to the Nisnevich direct image. -/
def nisnevichImageAdjunction : nisnevichInverseImage r A ⊣ nisnevichDirectImage r A :=
  ((forgetBaseAdjunction r).op.whiskerLeft (C := A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _)
    (Iso.refl _) (Iso.refl _)

end AlgebraicGeometry.Scheme.SmoothSite
