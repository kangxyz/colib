/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Modules.Invertible.BoundaryFrameReparametrize
public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryRootTransport

/-! # Exact recovery of the original square frame

Precomposing both maps out of the boundary and then reparametrizing back gives
the frame of the original square. This applies directly to the two maps of an
affine-presentation isomorphism, without replacing the original boundary diagram.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits
universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem square_can_cancel {C : Type*} [Category C]
    {A B D E F G : C} (a : A ≅ B) (d : D ≅ B) (v : B ≅ E)
    (b : A ≅ F) (a' : F ≅ E) (c : D ≅ G) (d' : G ≅ E)
    (h₁ : a ≪≫ v = b ≪≫ a') (h₂ : d ≪≫ v = c ≪≫ d') :
    a ≪≫ d.symm ≪≫ c = b ≪≫ a' ≪≫ d'.symm := by
  have hd : d.symm ≪≫ c = v ≪≫ d'.symm := by
    have H := congrArg (fun z => d.symm ≪≫ z ≪≫ d'.symm) h₂
    simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id,
      Iso.trans_refl] using H.symm
  rw [hd]
  simpa only [Iso.trans_assoc] using congrArg (fun z => z ≪≫ d'.symm) h₁

/-- The actual square comparison commutes with a named boundary reparametrization. -/
theorem pullbackSquareIso_boundaryReparametrize {A B D X Y : Scheme.{u}}
    (u : A ⟶ B) (b : B ⟶ D) (b' : A ⟶ D)
    (i : D ⟶ Y) (g : B ⟶ X) (h : A ⟶ X) (f : X ⟶ Y)
    (wb : u ≫ b = b') (wg : u ≫ g = h)
    (w : b ≫ i = g ≫ f) (w' : b' ≫ i = h ≫ f) (L : Y.Modules) :
    (pullback u).mapIso (pullbackSquareIso b i g f w L) ≪≫
      canIso u g h wg ((pullback f).obj L) =
    canIso u b b' wb ((pullback i).obj L) ≪≫ pullbackSquareIso b' i h f w' L := by
  have wt : u ≫ (g ≫ f) = h ≫ f := by rw [← Category.assoc, wg]
  have h₁ : (pullback u).mapIso (canIso b i (g ≫ f) w L) ≪≫
      canIso u (g ≫ f) (h ≫ f) wt L =
    canIso u b b' wb ((pullback i).obj L) ≪≫ canIso b' i (h ≫ f) w' L :=
    Iso.ext (canHom_comp u b i b' (g ≫ f) (h ≫ f) wb w w' wt L)
  have h₂ : (pullback u).mapIso (canIso g f (g ≫ f) rfl L) ≪≫
      canIso u (g ≫ f) (h ≫ f) wt L =
    canIso u g h wg ((pullback f).obj L) ≪≫ canIso h f (h ≫ f) rfl L :=
    Iso.ext (canHom_comp u g f h (g ≫ f) (h ≫ f) wg rfl rfl wt L)
  simpa only [pullbackSquareIso, Functor.mapIso_trans, Functor.mapIso_symm,
    Iso.trans_assoc] using square_can_cancel _ _ _ _ _ _ _ h₁ h₂

/-- Reparametrizing the concrete frame on the precomposed boundary recovers
exactly the frame from the original square, not merely some trivialization. -/
theorem boundaryFrameReparametrize_square {A B D X Y : Scheme.{u}}
    (u : A ⟶ B) (b : B ⟶ D) (b' : A ⟶ D)
    (i : D ⟶ Y) (g : B ⟶ X) (h : A ⟶ X) (f : X ⟶ Y)
    (wb : u ≫ b = b') (wg : u ≫ g = h)
    (w : b ≫ i = g ≫ f) (w' : b' ≫ i = h ≫ f) (L : Y.Modules)
    (τ : (pullback i).obj L ≅ SheafOfModules.unit D.ringCatSheaf) :
    boundaryFrameReparametrize u g h wg ((pullback f).obj L)
      (pullbackBoundaryTrivialization b i g f w L τ) =
    pullbackBoundaryTrivialization b' i h f w' L τ := by
  let c := canIso u b b' wb ((pullback i).obj L)
  let cu := canIso u b b' wb (SheafOfModules.unit D.ringCatSheaf)
  have hs : (canIso u g h wg ((pullback f).obj L)).symm ≪≫
      ((pullback u).mapIso (pullbackSquareIso b i g f w L)).symm =
    (pullbackSquareIso b' i h f w' L).symm ≪≫ c.symm := by
    have H := congrArg Iso.symm (pullbackSquareIso_boundaryReparametrize
      u b b' i g h f wb wg w w' L)
    simpa only [Iso.trans_symm] using H
  have hn : c.symm ≪≫ (pullback u).mapIso ((pullback b).mapIso τ) =
      (pullback b').mapIso τ ≪≫ cu.symm := by
    have H : (pullback u).mapIso ((pullback b).mapIso τ) ≪≫ cu =
        c ≪≫ (pullback b').mapIso τ :=
      Iso.ext (canHom_naturality u b b' wb τ.hom)
    have H' := congrArg (fun z => c.symm ≪≫ z ≪≫ cu.symm) H
    simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl,
      Iso.symm_self_id_assoc] using H'
  have hu := pullbackUnitIso_can u b b' wb
  have h₁ := congrArg (fun z => z ≪≫ (pullback u).mapIso ((pullback b).mapIso τ) ≪≫
    (pullback u).mapIso (pullbackUnitIso b) ≪≫ pullbackUnitIso u) hs
  have h₂ := congrArg (fun z => (pullbackSquareIso b' i h f w' L).symm ≪≫ z ≪≫
    (pullback u).mapIso (pullbackUnitIso b) ≪≫ pullbackUnitIso u) hn
  have h₃ := congrArg (fun z => (pullbackSquareIso b' i h f w' L).symm ≪≫
    (pullback b').mapIso τ ≪≫ cu.symm ≪≫ z) hu
  exact (by simpa only [boundaryFrameReparametrize, pullbackBoundaryTrivialization,
    Functor.mapIso_trans, Functor.mapIso_symm, Iso.trans_assoc] using h₁).trans
      ((by simpa only [Iso.trans_assoc] using h₂).trans
        (by simpa only [pullbackBoundaryTrivialization, Iso.trans_assoc,
          Iso.symm_self_id_assoc] using h₃))

end AlgebraicGeometry.Scheme.Modules
