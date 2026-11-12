/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.Diagram
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.MarkedGraphGeometry
public import Colib.AlgebraicGeometry.Divisors.FrameTransport

/-!
# The canonical graph frame on the genuinely refined relative curve

The complete marked graph square is Cartesian. Its kernel is therefore the
full comap of the original graph kernel. The native Cartier pullback comparison
preserves the actual canonical section. A frame constructed on the original
finite-product neighborhood transports to this literal new graph line.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Ample Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable {S X Z : Scheme.{u}} (q : X ⟶ S) (U : X.Opens) (V : S.Opens)
  (z : Z ⟶ X) (h : ∀ b : Z, (z ≫ q) b ∈ V → z b ∈ U)

local notation "q'" => parameterProjection q U V
local notation "z'" => markToParameter q U V z h
local notation "P" => pullback q (z ≫ q)
local notation "P'" => pullback q' (z' ≫ q')
local notation "iX" => Scheme.Opens.ι (parameterOpen q U V)
local notation "iZ" => Scheme.Opens.ι (markOpen q V z)

/-- The genuine comparison of the new full marked product with the old product. -/
def markedProductToOriginal : P' ⟶ P :=
  pullback.lift (pullback.fst _ _ ≫ iX) (pullback.snd _ _ ≫ iZ) (by
    rw [Category.assoc, ← parameterProjection_base, ← Category.assoc, pullback.condition,
      Category.assoc, Category.assoc, parameterProjection_base,
       markToParameter_original_assoc]
    exact (Category.assoc _ _ _).symm)

@[reassoc (attr := simp)]
theorem markedProductToOriginal_fst :
    markedProductToOriginal q U V z h ≫ pullback.fst q (z ≫ q) =
      pullback.fst _ _ ≫ iX := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem markedProductToOriginal_snd :
    markedProductToOriginal q U V z h ≫ pullback.snd q (z ≫ q) =
      pullback.snd _ _ ≫ iZ := pullback.lift_snd _ _ _

/-- The whole new marked graph is the literal Cartesian inverse image of the old one. -/
theorem markedGraphToOriginal_isPullback :
    IsPullback (relativeBoundaryGraph q' z') iZ
      (markedProductToOriginal q U V z h) (relativeBoundaryGraph q z) where
  w := by
    apply pullback.hom_ext
    · simp only [Category.assoc, markedProductToOriginal_fst, relativeBoundaryGraph_fst_assoc,
        relativeBoundaryGraph_fst, markToParameter_original]
    · simp only [Category.assoc, markedProductToOriginal_snd, relativeBoundaryGraph_snd_assoc,
        relativeBoundaryGraph_snd, Category.comp_id]
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun t => by
    have hf : t.fst ≫ pullback.fst q' (z' ≫ q') ≫ iX = t.snd ≫ z := by
      have hh := congrArg (fun m => m ≫ pullback.fst q (z ≫ q)) t.condition
      simpa only [Category.assoc, markedProductToOriginal_fst,
        relativeBoundaryGraph_fst] using hh
    have hs : t.fst ≫ pullback.snd q' (z' ≫ q') ≫ iZ = t.snd := by
      have hh := congrArg (fun m => m ≫ pullback.snd q (z ≫ q)) t.condition
      simpa only [Category.assoc, markedProductToOriginal_snd,
        relativeBoundaryGraph_snd, Category.comp_id] using hh
    refine ⟨t.fst ≫ pullback.snd q' (z' ≫ q'), ?_, hs, ?_⟩
    · apply pullback.hom_ext
      · change ((t.fst ≫ pullback.snd q' (z' ≫ q')) ≫ relativeBoundaryGraph q' z') ≫
          pullback.fst q' (z' ≫ q') = _
        simp only [Category.assoc, relativeBoundaryGraph_fst]
        apply (cancel_mono iX).mp
        let l := t.fst ≫ pullback.snd q' (z' ≫ q')
        let r := t.fst ≫ pullback.fst q' (z' ≫ q')
        have hl : l ≫ iZ = t.snd := (Category.assoc _ _ _).trans hs
        have hr : r ≫ iX = t.snd ≫ z := (Category.assoc _ _ _).trans hf
        calc
          _ = l ≫ z' ≫ iX := Category.assoc _ _ _
          _ = l ≫ iZ ≫ z := congrArg (fun m => l ≫ m) (markToParameter_original q U V z h)
          _ = (l ≫ iZ) ≫ z := (Category.assoc _ _ _).symm
          _ = t.snd ≫ z := congrArg (fun m => m ≫ z) hl
          _ = _ := hr.symm
      · change ((t.fst ≫ pullback.snd q' (z' ≫ q')) ≫ relativeBoundaryGraph q' z') ≫
          pullback.snd q' (z' ≫ q') = _
        simp only [Category.assoc, relativeBoundaryGraph_snd, Category.comp_id]
    · intro l hl _
      have hh := congrArg (fun m => m ≫ pullback.snd q' (z' ≫ q')) hl
      change (l ≫ relativeBoundaryGraph q' z') ≫ pullback.snd q' (z' ≫ q') =
        t.fst ≫ pullback.snd q' (z' ≫ q') at hh
      simpa only [Category.assoc, relativeBoundaryGraph_snd, Category.comp_id] using hh)⟩

/-- The full graph ideal, including its multiplicities, is the actual comap. -/
theorem markedGraphToOriginal_ideal [IsSeparated q] :
    (relativeBoundaryGraph q z).ker.comap (markedProductToOriginal q U V z h) =
      (relativeBoundaryGraph q' z').ker :=
  (ker_eq_comap_of_cartesian (markedGraphToOriginal_isPullback q U V z h)).symm

/-- The product comparison lands in the exact original graph-frame neighborhood. -/
def markedProductToFrameOpen : P' ⟶ ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι
    (markedProductToOriginal q U V z h) (by
      rintro _ ⟨t, rfl⟩
      have ht := congrArg (fun m => m t) (markedProductToOriginal_fst q U V z h)
      refine ⟨⟨markedProductToOriginal q U V z h t, ?_⟩, rfl⟩
      change pullback.fst q (z ≫ q) (markedProductToOriginal q U V z h t) ∈ U
      have ht' : pullback.fst q (z ≫ q) (markedProductToOriginal q U V z h t) =
          iX (pullback.fst q' (z' ≫ q') t) := ht
      exact ht'.symm ▸ (pullback.fst q' (z' ≫ q') t).property.1)

@[reassoc (attr := simp)]
theorem markedProductToFrameOpen_original :
    markedProductToFrameOpen q U V z h ≫ ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι =
      markedProductToOriginal q U V z h := IsOpenImmersion.lift_fac _ _ _

variable [IsSeparated q] [SmoothOfRelativeDimension 1 q]

/-- The actual native canonical graph line on the refined relative curve has the
constructed frame. The input here is the intermediate neighborhood frame, whose
unconditional producer is GraphNeighborhood.exists_simultaneousPrincipalBoundaryFrames. -/
def canonicalGraphFrame
    (e : (divisorSheaf (relativeBoundaryGraph q z).ker).restrict
      ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι ≅
        SheafOfModules.unit ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).toScheme.ringCatSheaf) :
    divisorSheaf (relativeBoundaryGraph q' z').ker ≅ SheafOfModules.unit (P').ringCatSheaf := by
  let D := (relativeBoundaryGraph q z).ker
  let m := markedProductToOriginal q U V z h
  let i := ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).ι
  let l := markedProductToFrameOpen q U V z h
  let e₀ : (Modules.pullback i).obj (divisorSheaf D) ≅
      SheafOfModules.unit ((pullback.fst q (z ≫ q)) ⁻¹ᵁ U).toScheme.ringCatSheaf :=
    ((Modules.restrictFunctorIsoPullback i).app (divisorSheaf D)).symm ≪≫ e
  let e₁ : (Modules.pullback m).obj (divisorSheaf D) ≅ SheafOfModules.unit (P').ringCatSheaf :=
    (Modules.pullbackCongr (markedProductToFrameOpen_original q U V z h).symm).app
        (divisorSheaf D) ≪≫
      ((Modules.pullbackComp l i).app (divisorSheaf D)).symm ≪≫ Modules.framePullback l e₀
  exact (divisorComapEqIso m D (relativeBoundaryGraph q' z').ker
    (markedGraphToOriginal_ideal q U V z h)).symm ≪≫ e₁

/-- The complete graph and coefficient frames exist on the same actual diagram.
This is over an arbitrary affine base, not only over a field. -/
theorem exists_canonicalGraph_and_coefficient_frames [IsAffine X] [IsAffine S]
    [IsFinite (z ≫ q)] {C D : Scheme.{u}} (π : C ⟶ S) (d : D ⟶ C)
    [IsFinite (d ≫ π)] (s : Z ⟶ C) (L : C.Modules) [IsInvertibleModule C L] (x : X) :
    ∃ u : Γ(X, ⊤), x ∈ X.basicOpen u ∧
      ∃ v : Γ(S, ⊤), q x ∈ S.basicOpen v ∧
        ∃ h : ∀ b : Z, (z ≫ q) b ∈ S.basicOpen v → z b ∈ X.basicOpen u,
          Nonempty (divisorSheaf (relativeBoundaryGraph
            (parameterProjection q (X.basicOpen u) (S.basicOpen v))
            (markToParameter q (X.basicOpen u) (S.basicOpen v) z h)).ker ≅
              SheafOfModules.unit (pullback
                (parameterProjection q (X.basicOpen u) (S.basicOpen v))
                (markToParameter q (X.basicOpen u) (S.basicOpen v) z h ≫
                  parameterProjection q (X.basicOpen u) (S.basicOpen v))).ringCatSheaf) ∧
          Nonempty (((Modules.pullback d).obj L).restrict
            ((d ≫ π) ⁻¹ᵁ S.basicOpen v).ι ≅
              SheafOfModules.unit ((d ≫ π) ⁻¹ᵁ S.basicOpen v).toScheme.ringCatSheaf) ∧
          Nonempty (((Modules.pullback s).obj L).restrict
            ((z ≫ q) ⁻¹ᵁ S.basicOpen v).ι ≅
              SheafOfModules.unit ((z ≫ q) ⁻¹ᵁ S.basicOpen v).toScheme.ringCatSheaf) := by
  obtain ⟨u, hxu, v, hxv, h, ⟨e⟩, eD, eZ⟩ :=
    exists_simultaneousPrincipalBoundaryFrames q z π d s L x
  exact ⟨u, hxu, v, hxv, h, ⟨canonicalGraphFrame q _ _ z h e⟩, eD, eZ⟩

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
