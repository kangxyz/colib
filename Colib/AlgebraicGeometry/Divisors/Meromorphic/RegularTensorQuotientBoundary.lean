/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.RegularTensorQuotient
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.CompatibleBoundaryFrames
public import StacksFrontier.AlgebraicGeometry.Divisors.PullbackTensorTrivialization
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk

/-!
# Full-boundary frames of the ordinary tensor quotient

All pullbacks below are pullbacks of ordinary sections on the actual nonvanishing open.
Neither the ambient scheme nor the boundary is assumed reduced or integral.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules.Invertible
open scoped TensorProduct

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry.Scheme.Modules

/-- The left unitor of the unit module also computes a pure tensor with right factor one. -/
theorem unitLeftUnitor_tensor_right_one (B : Scheme.{u}) (W : B.Opens) (r : Γ(B, W)) :
    Hom.app (tensorProductLeftUnitor B.sheaf.obj B.ringCatSheaf.property
      (SheafOfModules.unit B.ringCatSheaf)).hom W
      (Stacks.SheafOfModules.tensorSectionsAt B.sheaf.obj B.ringCatSheaf.property (op W)
        (SheafOfModules.unit B.ringCatSheaf) (SheafOfModules.unit B.ringCatSheaf) r
        (1 : Γ(B, W))) = r := by
  have ht : Stacks.SheafOfModules.tensorSectionsAt B.sheaf.obj B.ringCatSheaf.property (op W)
        (SheafOfModules.unit B.ringCatSheaf) (SheafOfModules.unit B.ringCatSheaf) r
        (1 : Γ(B, W)) =
      Stacks.SheafOfModules.tensorSectionsAt B.sheaf.obj B.ringCatSheaf.property (op W)
        (SheafOfModules.unit B.ringCatSheaf) (SheafOfModules.unit B.ringCatSheaf)
        (1 : Γ(B, W)) r := by
    unfold Stacks.SheafOfModules.tensorSectionsAt
    congr 1
    change r ⊗ₜ[Γ(B, W)] (1 : Γ(B, W)) = (1 : Γ(B, W)) ⊗ₜ[Γ(B, W)] r
    simpa only [smul_eq_mul, mul_one] using
      (TensorProduct.smul_tmul (R := Γ(B, W)) r (1 : Γ(B, W)) (1 : Γ(B, W)))
  refine (congrArg (Hom.app (tensorProductLeftUnitor B.sheaf.obj B.ringCatSheaf.property
    (SheafOfModules.unit B.ringCatSheaf)).hom W) ht).trans ?_
  exact Stacks.SheafOfModules.tensorSections_leftUnitorAt B.sheaf.obj B.ringCatSheaf.property
    (op W) (SheafOfModules.unit B.ringCatSheaf) r

/-- A denominator framed as one does not change the frame coordinate of a tensor section
under the actual pullback/tensor comparison. -/
theorem pullbackTensorFrame_tensorSection_of_right_one {X B : Scheme.{u}} (i : B ⟶ X)
    (L N : X.Modules) (U : X.Opens)
    (e : (pullback i).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (m : Γ(L, U)) (b : Γ(N, U))
    (hb : Hom.app eN.hom (i ⁻¹ᵁ U) (pullbackSectionHom i N U (i ⁻¹ᵁ U) le_rfl b) =
      (1 : Γ(B, i ⁻¹ᵁ U))) :
    Hom.app (pullbackTensorFrame i L N e eN).hom (i ⁻¹ᵁ U)
      (pullbackSectionHom i (tensorObj L N) U (i ⁻¹ᵁ U) le_rfl
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
          L N m b)) =
      Hom.app e.hom (i ⁻¹ᵁ U) (pullbackSectionHom i L U (i ⁻¹ᵁ U) le_rfl m) := by
  let W := i ⁻¹ᵁ U
  let lunit := tensorProductLeftUnitor B.sheaf.obj B.ringCatSheaf.property
    (SheafOfModules.unit B.ringCatSheaf)
  let E := tensorProductIso B.sheaf.obj B.ringCatSheaf.property e eN
  change Hom.app lunit.hom W (Hom.app E.hom W
    (Hom.app (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso i L N).hom W
      (pullbackSectionHom i (tensorObj L N) U W le_rfl
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
          L N m b)))) = _
  refine (congrArg (fun z => Hom.app lunit.hom W (Hom.app E.hom W z))
    (Stacks.PullbackTensorIso.pullbackSectionHom_tensorSectionsAt i L N U m b)).trans ?_
  refine (congrArg (Hom.app lunit.hom W)
    (Stacks.SheafOfModules.tensorSections_tensorProductIsoAt B.sheaf.obj B.ringCatSheaf.property
      (op W) _ _ _ _ e eN _ _)).trans ?_
  refine (congrArg (fun z => Hom.app lunit.hom W
    (Stacks.SheafOfModules.tensorSectionsAt B.sheaf.obj B.ringCatSheaf.property (op W)
      (SheafOfModules.unit B.ringCatSheaf) (SheafOfModules.unit B.ringCatSheaf)
      (Hom.app e.hom W (pullbackSectionHom i L U W le_rfl m)) z)) hb).trans ?_
  exact unitLeftUnitor_tensor_right_one B W _

/-- The ordinary quotient has frame coordinate one on the entire inverse-image open,
when both original sections have their prescribed compatible coordinates there. -/
@[colib_tag "COL-1052"]
theorem frame_regularTensorQuotientOnOpen_preimage {X B : Scheme.{u}} (i : B ⟶ X)
    (L N : X.Modules) (b : N.sections) (U : X.Opens)
    [IsIso ((N.unitHomEquiv.symm b).over U)]
    (e : (pullback i).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (a : Γ(tensorObj L N, U))
    (ha : Hom.app (pullbackTensorFrame i L N e eN).hom (i ⁻¹ᵁ U)
      (pullbackSectionHom i (tensorObj L N) U (i ⁻¹ᵁ U) le_rfl a) =
        (1 : Γ(B, i ⁻¹ᵁ U)))
    (hb : Hom.app eN.hom (i ⁻¹ᵁ U)
      (pullbackSectionHom i N U (i ⁻¹ᵁ U) le_rfl (b.eval (op U))) =
        (1 : Γ(B, i ⁻¹ᵁ U))) :
    Hom.app e.hom (i ⁻¹ᵁ U)
      (pullbackSectionHom i L U (i ⁻¹ᵁ U) le_rfl
        (regularTensorQuotientOnOpen X L N b U a)) = (1 : Γ(B, i ⁻¹ᵁ U)) := by
  refine (pullbackTensorFrame_tensorSection_of_right_one i L N U e eN _ _ hb).symm.trans ?_
  exact (congrArg (fun t => Hom.app (pullbackTensorFrame i L N e eN).hom (i ⁻¹ᵁ U)
    (pullbackSectionHom i (tensorObj L N) U (i ⁻¹ᵁ U) le_rfl t))
    (tensorSection_regularTensorQuotientOnOpen X L N b U a)).trans ha

/-- A boundary frame equal to one forces the entire boundary into the original
nonvanishing open. The assertion is about the original morphism, without reduction. -/
@[colib_tag "COL-1052"]
theorem preimage_nonvanishingOpen_eq_top_of_boundary_frame {X B : Scheme.{u}} (i : B ⟶ X)
    (N : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N]
    (b : N.sections)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (hb : Hom.app eN.hom ⊤ (pullbackGlobalSections i N (b.eval (op ⊤))) =
      (1 : Γ(B, ⊤))) :
    i ⁻¹ᵁ Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) N b = ⊤ := by
  apply top_unique
  intro z _
  change i.base z ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) N b
  rw [Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq]
  have hpb : z ∈ Stacks.Ample.nonvanishingLocus ((pullback i).obj N)
      (pullbackGlobalSections i N (b.eval (op ⊤))) := by
    apply (Stacks.Ample.nonvanishingLocus_congr eN _).subset
    exact Stacks.Ample.Γgerm_notMem_maximalSmul_of_eq_one B z _ hb.symm
  exact (Set.ext_iff.mp
    (Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections i N
      (b.eval (op ⊤))) z).mpr hpb

/-- A global pullback frame coordinate of one remains one over the full inverse image
of an arbitrary open. -/
theorem frame_pullbackSectionHom_resTop_eq_one {X B : Scheme.{u}} (i : B ⟶ X)
    (M : X.Modules) (U : X.Opens)
    (e : (pullback i).obj M ≅ SheafOfModules.unit B.ringCatSheaf) (a : Γ(M, ⊤))
    (ha : Hom.app e.hom ⊤ (pullbackGlobalSections i M a) = (1 : Γ(B, ⊤))) :
    Hom.app e.hom (i ⁻¹ᵁ U)
      (pullbackSectionHom i M U (i ⁻¹ᵁ U) le_rfl
        (M.presheaf.map (homOfLE le_top).op a)) = (1 : Γ(B, i ⁻¹ᵁ U)) := by
  refine (congrArg (Hom.app e.hom (i ⁻¹ᵁ U))
    (pullbackSectionHom_resTop i M U a)).trans ?_
  refine (PresheafOfModules.naturality_apply e.hom.val
    (homOfLE (le_top : i ⁻¹ᵁ U ≤ ⊤)).op (pullbackGlobalSections i M a)).trans ?_
  exact (congrArg (fun t => (B.presheaf.map (homOfLE (le_top : i ⁻¹ᵁ U ≤ ⊤)).op).hom t)
    ha).trans (map_one _)

/-- On the full preimage of the original denominator open, the actual ordinary quotient
has the given original frame coordinate one. -/
@[colib_tag "COL-1052"]
theorem frame_regularTensorQuotientOnNonvanishingOpen_preimage
    {X B : Scheme.{u}} (i : B ⟶ X) (L N : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N]
    (b : N.sections)
    (e : (pullback i).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (a : Γ(tensorObj L N, ⊤))
    (ha : Hom.app (pullbackTensorFrame i L N e eN).hom ⊤
      (pullbackGlobalSections i (tensorObj L N) a) = (1 : Γ(B, ⊤)))
    (hb : Hom.app eN.hom ⊤ (pullbackGlobalSections i N (b.eval (op ⊤))) =
      (1 : Γ(B, ⊤))) :
    let V := Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) N b
    Hom.app e.hom (i ⁻¹ᵁ V)
      (pullbackSectionHom i L V (i ⁻¹ᵁ V) le_rfl
        (regularTensorQuotientOnNonvanishingOpen X L N b a)) = (1 : Γ(B, i ⁻¹ᵁ V)) := by
  let V := Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) N b
  let := Stacks.SheafOfModules.Scheme.isIso_over_nonvanishingOpen X N b
  apply frame_regularTensorQuotientOnOpen_preimage i L N b V e eN
  · exact frame_pullbackSectionHom_resTop_eq_one i (tensorObj L N) V
      (pullbackTensorFrame i L N e eN) a ha
  · have heval : b.eval (op V) = N.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        (b.eval (op ⊤)) :=
      (PresheafOfModules.sections_property b (homOfLE (le_top : V ≤ ⊤)).op).symm
    exact (congrArg (fun t => Hom.app eN.hom (i ⁻¹ᵁ V)
      (pullbackSectionHom i N V (i ⁻¹ᵁ V) le_rfl t)) heval).trans
      (frame_pullbackSectionHom_resTop_eq_one i N V eN (b.eval (op ⊤)) hb)

/-- The actual pullback of the ordinary quotient to the whole original boundary.
Its domain is justified by the denominator's prescribed full-boundary frame. -/
def boundaryRegularTensorQuotient {X B : Scheme.{u}} (i : B ⟶ X) (L N : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N]
    (b : N.sections)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (hb : Hom.app eN.hom ⊤ (pullbackGlobalSections i N (b.eval (op ⊤))) =
      (1 : Γ(B, ⊤))) (a : Γ(tensorObj L N, ⊤)) : Γ((pullback i).obj L, ⊤) :=
  pullbackSectionHom i L
    (Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) N b) ⊤
    (preimage_nonvanishingOpen_eq_top_of_boundary_frame i N b eN hb).ge
    (regularTensorQuotientOnNonvanishingOpen X L N b a)

/-- The original frame of `L` reads the actual quotient as one on the full boundary,
including all its nilpotents. This uses regular sections, never a pullback of a generic field. -/
@[colib_tag "COL-1052",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/Divisors/PullbackTensorTrivialization.lean:133-152"
    "ingredient" "Native pullback tensor comparison on the whole inverse-image open",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/NonvanishingPullback/GlobalSections.lean:62-67"
    "ingredient" "Nonvanishing loci commute with actual pullback of global sections"]
theorem frame_boundaryRegularTensorQuotient_eq_one {X B : Scheme.{u}} (i : B ⟶ X)
    (L N : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N]
    (b : N.sections)
    (e : (pullback i).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (a : Γ(tensorObj L N, ⊤))
    (ha : Hom.app (pullbackTensorFrame i L N e eN).hom ⊤
      (pullbackGlobalSections i (tensorObj L N) a) = (1 : Γ(B, ⊤)))
    (hb : Hom.app eN.hom ⊤ (pullbackGlobalSections i N (b.eval (op ⊤))) =
      (1 : Γ(B, ⊤))) :
    Hom.app e.hom ⊤ (boundaryRegularTensorQuotient i L N b eN hb a) = (1 : Γ(B, ⊤)) := by
  let V := Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) N b
  have hW : ∀ (W : B.Opens), W = i ⁻¹ᵁ V → ∀ h : W ≤ i ⁻¹ᵁ V,
      Hom.app e.hom W (pullbackSectionHom i L V W h
        (regularTensorQuotientOnNonvanishingOpen X L N b a)) = (1 : Γ(B, W)) := by
    intro W hW h
    subst W
    exact frame_regularTensorQuotientOnNonvanishingOpen_preimage i L N b e eN a ha hb
  exact hW ⊤ (preimage_nonvanishingOpen_eq_top_of_boundary_frame i N b eN hb).symm _

end AlgebraicGeometry.Scheme.Modules
