/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryRoot
public import Colib.AlgebraicGeometry.Divisors.FrameTransport
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer.GlobalSections
public import StacksFrontier.AlgebraicGeometry.IdealOfClosedSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-! # Full-boundary normalization of sections defined on an ambient open

The ambient section need only be defined near the boundary. Both its iterated
pullbacks and the specified square comparison are retained.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem pullbackCongr_openSection {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (w : f = g) (M : Y.Modules) (U : Y.Opens) (V : X.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) (s : Γ(M, U)) :
    Hom.app ((pullbackCongr w).app M).hom V
      (pullbackSectionHom f M U V hf s) = pullbackSectionHom g M U V hg s := by
  subst g
  rfl

/-- The canonical composite comparison preserves pullbacks of sections over arbitrary opens. -/
theorem canIso_pullbackSectionHom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (p : X ⟶ Z) (hp : f ≫ g = p)
    (M : Z.Modules) (U : Z.Opens) (W : Y.Opens) (V : X.Opens)
    (hg : W ≤ g ⁻¹ᵁ U) (hf : V ≤ f ⁻¹ᵁ W) (hv : V ≤ p ⁻¹ᵁ U)
    (s : Γ(M, U)) :
    Hom.app (canIso f g p hp M).hom V
      (pullbackSectionHom f ((pullback g).obj M) W V hf
        (pullbackSectionHom g M U W hg s)) = pullbackSectionHom p M U V hv s := by
  have hc : V ≤ (f ≫ g) ⁻¹ᵁ U := hf.trans (Scheme.Hom.preimage_mono f hg)
  change Hom.app ((pullbackCongr hp).app M).hom V
    (Hom.app ((pullbackComp f g).app M).hom V
      (pullbackSectionHom f ((pullback g).obj M) W V hf
        (pullbackSectionHom g M U W hg s))) = _
  exact (congrArg (Hom.app ((pullbackCongr hp).app M).hom V)
    (pullbackSection_comp f g M U W V hg hf hc s)).trans
      (pullbackCongr_openSection hp M U V hc hv s)

/-- The original square comparison preserves sections defined on arbitrary compatible opens. -/
theorem pullbackSquareIso_pullbackSectionHom {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D)
    (w : f ≫ g = h ≫ k) (M : D.Modules)
    (U : D.Opens) (V : B.Opens) (W : C.Opens) (T : A.Opens)
    (hg : V ≤ g ⁻¹ᵁ U) (hf : T ≤ f ⁻¹ᵁ V)
    (hk : W ≤ k ⁻¹ᵁ U) (hh : T ≤ h ⁻¹ᵁ W) (s : Γ(M, U)) :
    Hom.app (pullbackSquareIso f g h k w M).hom T
      (pullbackSectionHom f ((pullback g).obj M) V T hf
        (pullbackSectionHom g M U V hg s)) =
      pullbackSectionHom h ((pullback k).obj M) W T hh
        (pullbackSectionHom k M U W hk s) := by
  have ht : T ≤ (h ≫ k) ⁻¹ᵁ U := hh.trans (Scheme.Hom.preimage_mono h hk)
  change Hom.app (canIso h k (h ≫ k) rfl M).inv T
    (Hom.app (canIso f g (h ≫ k) w M).hom T _) = _
  exact (congrArg (Hom.app (canIso h k (h ≫ k) rfl M).inv T)
    (canIso_pullbackSectionHom f g (h ≫ k) w M U V T hg hf ht s)).trans
      ((congrArg (Hom.app (canIso h k (h ≫ k) rfl M).inv T)
        (canIso_pullbackSectionHom h k (h ≫ k) rfl M U W T hk hh ht s)).symm.trans
          (app_inv_app (canIso h k (h ≫ k) rfl M) T _))

private theorem pullbackSectionHom_top_eq_global {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (ht : ⊤ ≤ f ⁻¹ᵁ ⊤) :
    pullbackSectionHom f M ⊤ ⊤ ht = pullbackGlobalSections f M := by
  unfold pullbackSectionHom pullbackGlobalSections
  congr 2

/-- A section defined on an ambient open, normalized on the entire original boundary,
remains normalized in the literal square-pullback frame on the entire new boundary. -/
theorem pullbackBoundaryTrivialization_openSection_one {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D)
    (w : f ≫ g = h ≫ k) (N : D.Modules)
    (e : (pullback g).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (U : D.Opens) (W : C.Opens) (hg : ⊤ ≤ g ⁻¹ᵁ U)
    (hk : W ≤ k ⁻¹ᵁ U) (hh : ⊤ ≤ h ⁻¹ᵁ W) (s : Γ(N, U))
    (hs : Hom.app e.hom ⊤ (pullbackSectionHom g N U ⊤ hg s) = (1 : Γ(B, ⊤))) :
    Hom.app (pullbackBoundaryTrivialization f g h k w N e).hom ⊤
      (pullbackSectionHom h ((pullback k).obj N) W ⊤ hh
        (pullbackSectionHom k N U W hk s)) = (1 : Γ(A, ⊤)) := by
  have hf : ⊤ ≤ f ⁻¹ᵁ ⊤ := by simp
  have hp := pullbackSquareIso_pullbackSectionHom f g h k w N U ⊤ W ⊤ hg hf hk hh s
  rw [pullbackSectionHom_top_eq_global f _ hf] at hp
  have hi := (congrArg (Hom.app (pullbackSquareIso f g h k w N).inv ⊤) hp).symm.trans
    (app_inv_app (pullbackSquareIso f g h k w N) ⊤ _)
  change Hom.app (pullbackUnitIso f).hom ⊤
    (Hom.app ((pullback f).map e.hom) ⊤
      (Hom.app (pullbackSquareIso f g h k w N).inv ⊤ _)) = _
  rw [hi]
  exact (framePullback_coordinate f e (pullbackSectionHom g N U ⊤ hg s)).trans
    ((congrArg (fun z => f.appTop z) hs).trans (map_one f.appTop.hom))


end AlgebraicGeometry.Scheme.Modules
