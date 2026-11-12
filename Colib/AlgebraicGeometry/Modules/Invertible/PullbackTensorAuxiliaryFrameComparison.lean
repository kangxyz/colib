/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.Invertible.PullbackTensorFrameComparison
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.AuxiliaryPairFrames

/-!
# The original auxiliary contraction through a full-boundary square

The actual auxiliary frame contracts only the second tensor factor. Its pullback
commutes with the original boundary-square comparison without requiring any root
frame at the finite stage. A root frame available only on the limit can therefore
be composed with this equality afterwards.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.SheafOfModules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem tensor_iso_trans {D : Type*} [Category D] (T : D × D ⥤ D)
    {A B C P Q R : D} (a : A ≅ B) (b : B ≅ C) (p : P ≅ Q) (q : Q ≅ R) :
    T.mapIso (Iso.prod a p) ≪≫ T.mapIso (Iso.prod b q) =
      T.mapIso (Iso.prod (a ≪≫ b) (p ≪≫ q)) :=
  Iso.ext (T.map_comp (Iso.prod a p).hom (Iso.prod b q).hom).symm

private theorem right_unitor_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    (pullback f).mapIso (tensorProductRightUnitor Y.presheaf Y.ringCatIsSheaf M) =
      Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f M
          (SheafOfModules.unit Y.ringCatSheaf) ≪≫
        tensorProductIso X.presheaf X.ringCatIsSheaf (Iso.refl ((pullback f).obj M))
          (pullbackUnitIso f) ≪≫
          tensorProductRightUnitor X.presheaf X.ringCatIsSheaf ((pullback f).obj M) := by
  let : MonoidalCategory X.Modules :=
    Stacks.PullbackGradedAlgebra.monoidalCategory X.toRingedSpace
  have ht := (Stacks.SheafOfModules.tensorSheafMapIso_hom_eq X.presheaf X.ringCatIsSheaf
    (Iso.refl ((pullback f).obj M)) (pullbackUnitIso f)).trans
      ((MonoidalCategory.id_tensorHom ((pullback f).obj M) (pullbackUnitIso f).hom).trans
        (Stacks.SheafOfModules.whiskerLeft_eq_sheafify_map X.presheaf X.ringCatIsSheaf
          ((pullback f).obj M) (pullbackUnitIso f).hom))
  exact Iso.ext ((pullbackTensorProductRightUnitor_hom f M).trans
    (congrArg (fun z => (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f M
      (SheafOfModules.unit Y.ringCatSheaf)).hom ≫ z ≫
        (tensorProductRightUnitor X.presheaf X.ringCatIsSheaf ((pullback f).obj M)).hom)
      ht.symm))

private theorem right_unitor_naturality {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    tensorProductIso X.presheaf X.ringCatIsSheaf e
        (Iso.refl (SheafOfModules.unit X.ringCatSheaf)) ≪≫
      tensorProductRightUnitor X.presheaf X.ringCatIsSheaf N =
    tensorProductRightUnitor X.presheaf X.ringCatIsSheaf M ≪≫ e := by
  let : MonoidalCategory X.Modules :=
    Stacks.PullbackGradedAlgebra.monoidalCategory X.toRingedSpace
  have ht := (Stacks.SheafOfModules.tensorSheafMapIso_hom_eq X.presheaf X.ringCatIsSheaf
    e (Iso.refl (SheafOfModules.unit X.ringCatSheaf))).trans
      (MonoidalCategory.tensorHom_id e.hom (SheafOfModules.unit X.ringCatSheaf))
  have hM := congrArg Iso.hom
    (Stacks.SheafOfModules.Strict_rightUnitor_eq X.presheaf X.ringCatIsSheaf M)
  have hN := congrArg Iso.hom
    (Stacks.SheafOfModules.Strict_rightUnitor_eq X.presheaf X.ringCatIsSheaf N)
  exact Iso.ext ((congrArg₂ (fun a b => a ≫ b) ht hN.symm).trans
    ((MonoidalCategory.rightUnitor_naturality e.hom).trans
      (congrArg (fun z => z ≫ e.hom) hM)))

private theorem contraction_pullback {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : D × D ⥤ D) {A B P : C} {Q U V : D}
    (a : A ≅ B) (b : B ≅ P) (s : F.obj A ≅ T.obj (F.obj P, Q))
    (t : F.obj B ≅ T.obj (F.obj P, U)) (n : Q ≅ U) (u : U ≅ V)
    (r : T.obj (F.obj P, V) ≅ F.obj P)
    (hn : F.mapIso a ≪≫ t = s ≪≫ T.mapIso (Iso.prod (Iso.refl _) n))
    (hu : F.mapIso b = t ≪≫ T.mapIso (Iso.prod (Iso.refl _) u) ≪≫ r) :
    F.mapIso (a ≪≫ b) =
      s ≪≫ T.mapIso (Iso.prod (Iso.refl _) (n ≪≫ u)) ≪≫ r := by
  rw [F.mapIso_trans, hu]
  simp only [← Iso.trans_assoc] at hn ⊢
  rw [hn]
  simp only [Iso.trans_assoc]
  rw [← Iso.trans_assoc (T.mapIso _), tensor_iso_trans]
  simp only [Iso.refl_trans]

private theorem map_refl_naturality {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : D × D ⥤ D) {P : C} {A B U V : D}
    (a : A ≅ B) (b : B ≅ T.obj (F.obj P, U))
    (c : A ≅ T.obj (F.obj P, V)) (n : V ≅ U)
    (h : a ≪≫ b = c ≪≫ T.mapIso (Iso.prod (F.mapIso (Iso.refl P)) n)) :
    a ≪≫ b = c ≪≫ T.mapIso (Iso.prod (Iso.refl _) n) := by
  simpa only [Functor.mapIso_refl] using h

private theorem auxiliary_square {D : Type*} [Category D] (T : D × D ⥤ D)
    {Z W H K P Q R S U : D}
    (x : Z ≅ W) (y : W ≅ T.obj (P, Q)) (z : Z ≅ H) (k : H ≅ K)
    (t : K ≅ T.obj (R, S)) (a : P ≅ R) (b : Q ≅ S) (n : Q ≅ U)
    (rP : T.obj (P, U) ≅ P) (rR : T.obj (R, U) ≅ R)
    (hs : x ≪≫ y ≪≫ T.mapIso (Iso.prod a b) = z ≪≫ k ≪≫ t)
    (hn : T.mapIso (Iso.prod a (Iso.refl U)) ≪≫ rR = rP ≪≫ a) :
    x ≪≫ y ≪≫ T.mapIso (Iso.prod (Iso.refl P) n) ≪≫ rP ≪≫ a =
      z ≪≫ k ≪≫ t ≪≫ T.mapIso (Iso.prod (Iso.refl R) (b.symm ≪≫ n)) ≪≫ rR := by
  have H := congrArg (fun q => q ≪≫
    T.mapIso (Iso.prod (Iso.refl R) (b.symm ≪≫ n)) ≪≫ rR) hs
  simp only [Iso.trans_assoc] at H
  rw [← Iso.trans_assoc (T.mapIso _), tensor_iso_trans] at H
  simp only [Iso.trans_refl, Iso.self_symm_id_assoc] at H
  rw [← hn]
  rw [← Iso.trans_assoc (T.mapIso _), tensor_iso_trans]
  simpa only [Iso.refl_trans, Iso.trans_refl] using H

private theorem map_contraction_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {P Q R M : C} {A B S : D}
    (a : P ≅ Q) (b : Q ≅ R) (c : R ≅ M)
    (d : F.obj Q ≅ A) (e : A ≅ B) (f : B ≅ F.obj M)
    (s : F.obj M ≅ S) (v : F.obj P ≅ S)
    (hc : F.mapIso (b ≪≫ c) = d ≪≫ e ≪≫ f)
    (hs : F.mapIso a ≪≫ d ≪≫ e ≪≫ f ≪≫ s = v) :
    F.mapIso (a ≪≫ b ≪≫ c) ≪≫ s = v := by
  rw [F.mapIso_trans, Iso.trans_assoc, hc]
  simpa only [Iso.trans_assoc] using hs

set_option maxHeartbeats 800000 in
-- The auxiliary factor is framed, but the root factor has no stage frame hypothesis.
/-- Pulling back the original auxiliary contraction through the full-boundary square
commutes with its actual root-module comparison. No root frame at the stage is needed. -/
theorem pullbackTensorAuxiliaryFrame_square {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D) (w : f ≫ g = h ≫ k)
    (L N : D.Modules)
    (eN : (pullback g).obj N ≅ SheafOfModules.unit B.ringCatSheaf) :
    (pullback f).mapIso (pullbackTensorAuxiliaryFrame g L N eN) ≪≫
        pullbackSquareIso f g h k w L =
      pullbackSquareIso f g h k w
          (((Stacks.SheafOfModules.Tensor.sheafTensor D.sheaf).obj L).obj N) ≪≫
        (pullback h).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso k L N) ≪≫
          pullbackTensorAuxiliaryFrame h ((pullback k).obj L) ((pullback k).obj N)
            (pullbackBoundaryTrivialization f g h k w N eN) := by
  let T := tensorProductBifunctor A.sheaf.obj A.ringCatSheaf.property
  have hn := map_refl_naturality (pullback f) T
    ((pullback f).mapIso
      (tensorProductIso B.sheaf.obj B.ringCatSheaf.property
        (Iso.refl ((pullback g).obj L)) eN))
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
      ((pullback g).obj L) (SheafOfModules.unit B.ringCatSheaf))
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
      ((pullback g).obj L) ((pullback g).obj N))
    ((pullback f).mapIso eN)
    (pullbackTensorIso_tensorProductIso f (Iso.refl ((pullback g).obj L)) eN)
  have hc := contraction_pullback (pullback f) T
    (tensorProductIso B.sheaf.obj B.ringCatSheaf.property
      (Iso.refl ((pullback g).obj L)) eN)
    (tensorProductRightUnitor B.sheaf.obj B.ringCatSheaf.property ((pullback g).obj L))
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
      ((pullback g).obj L) ((pullback g).obj N))
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
      ((pullback g).obj L) (SheafOfModules.unit B.ringCatSheaf))
    ((pullback f).mapIso eN) (pullbackUnitIso f)
    (tensorProductRightUnitor A.sheaf.obj A.ringCatSheaf.property
      ((pullback f).obj ((pullback g).obj L))) hn
    (right_unitor_pullback f ((pullback g).obj L))
  have hs := auxiliary_square T
    ((pullback f).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N))
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
      ((pullback g).obj L) ((pullback g).obj N))
    (pullbackSquareIso f g h k w
      (((Stacks.SheafOfModules.Tensor.sheafTensor D.sheaf).obj L).obj N))
    ((pullback h).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso k L N))
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso h
      ((pullback k).obj L) ((pullback k).obj N))
    (pullbackSquareIso f g h k w L) (pullbackSquareIso f g h k w N)
    ((pullback f).mapIso eN ≪≫ pullbackUnitIso f)
    (tensorProductRightUnitor A.sheaf.obj A.ringCatSheaf.property
      ((pullback f).obj ((pullback g).obj L)))
    (tensorProductRightUnitor A.sheaf.obj A.ringCatSheaf.property
      ((pullback h).obj ((pullback k).obj L)))
    (pullbackSquareIso_tensorProduct f g h k w L N)
    (right_unitor_naturality (pullbackSquareIso f g h k w L))
  exact map_contraction_square (pullback f)
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N)
    (tensorProductIso B.sheaf.obj B.ringCatSheaf.property
      (Iso.refl ((pullback g).obj L)) eN)
    (tensorProductRightUnitor B.sheaf.obj B.ringCatSheaf.property ((pullback g).obj L))
    _ _ _ (pullbackSquareIso f g h k w L) _ hc hs

end AlgebraicGeometry.Scheme.Modules
