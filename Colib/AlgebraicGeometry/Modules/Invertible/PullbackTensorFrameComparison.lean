/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.Limits.BoundaryRoot
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.CompatibleBoundaryFrames

/-!
# The original tensor frame through a full-boundary square

The actual pullback tensor comparison commutes with the original boundary-square
comparison. Consequently the original product frame pulls back to the product of
its two original pulled-back frames. No replacement frame or compatibility premise
is introduced, and neither the ambient scheme nor its boundary is reduced.
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

private theorem tensor_can {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (p : W ⟶ Y) (hp : f ≫ g = p) (L N : Y.Modules) :
    canIso f g p hp (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj L).obj N) ≪≫
        Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso p L N =
      (pullback f).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N) ≪≫
        Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
          ((pullback g).obj L) ((pullback g).obj N) ≪≫
          tensorProductIso W.sheaf.obj W.ringCatSheaf.property
            (canIso f g p hp L) (canIso f g p hp N) := by
  subst p
  apply Iso.ext
  have H := pullbackTensorIso_comp f g L N
  have ht := Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map W.sheaf
    ((pullbackComp f g).hom.app L) ((pullbackComp f g).hom.app N)
  exact H.trans (congrArg
    (fun z => (pullback f).map
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N).hom ≫
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
        ((pullback g).obj L) ((pullback g).obj N)).hom ≫ z) ht)

private theorem tensor_square {D : Type*} [Category D] (T : D × D ⥤ D)
    {P Q R A B C A' B' C' : D} (c : P ≅ R) (d : Q ≅ R)
    (a : A ≅ C) (b : B ≅ C) (a' : A' ≅ C') (b' : B' ≅ C')
    (s : P ≅ T.obj (A, A')) (t : Q ≅ T.obj (B, B')) (r : R ≅ T.obj (C, C'))
    (hs : c ≪≫ r = s ≪≫ T.mapIso (Iso.prod a a'))
    (ht : d ≪≫ r = t ≪≫ T.mapIso (Iso.prod b b')) :
    s ≪≫ T.mapIso (Iso.prod (a ≪≫ b.symm) (a' ≪≫ b'.symm)) =
      c ≪≫ d.symm ≪≫ t := by
  rw [← tensor_iso_trans]
  have H : d.symm ≪≫ t = r ≪≫ T.mapIso (Iso.prod b.symm b'.symm) := by
    have h := congrArg (fun z => d.symm ≪≫ z ≪≫
      T.mapIso (Iso.prod b.symm b'.symm)) ht
    simpa [Iso.trans_assoc, tensor_iso_trans,
      show (Iso.refl B).prod (Iso.refl B') = Iso.refl (B, B') from rfl] using h.symm
  rw [← Iso.trans_assoc, ← hs, Iso.trans_assoc, ← H]

set_option maxHeartbeats 600000 in
-- The comparison retains the original modules along both paths of the square.
/-- The original square comparison commutes with the actual tensor pullback comparison. -/
theorem pullbackSquareIso_tensorProduct {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D) (w : f ≫ g = h ≫ k)
    (L N : D.Modules) :
    (pullback f).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N) ≪≫
      Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
        ((pullback g).obj L) ((pullback g).obj N) ≪≫
      tensorProductIso A.sheaf.obj A.ringCatSheaf.property
        (pullbackSquareIso f g h k w L) (pullbackSquareIso f g h k w N) =
    pullbackSquareIso f g h k w
        (((Stacks.SheafOfModules.Tensor.sheafTensor D.sheaf).obj L).obj N) ≪≫
      (pullback h).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso k L N) ≪≫
        Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso h
          ((pullback k).obj L) ((pullback k).obj N) := by
  have hs := tensor_square (tensorProductBifunctor A.sheaf.obj A.ringCatSheaf.property)
    (canIso f g (h ≫ k) w
      (((Stacks.SheafOfModules.Tensor.sheafTensor D.sheaf).obj L).obj N))
    (canIso h k (h ≫ k) rfl
      (((Stacks.SheafOfModules.Tensor.sheafTensor D.sheaf).obj L).obj N))
    (canIso f g (h ≫ k) w L) (canIso h k (h ≫ k) rfl L)
    (canIso f g (h ≫ k) w N) (canIso h k (h ≫ k) rfl N)
    ((pullback f).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N) ≪≫
      Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
        ((pullback g).obj L) ((pullback g).obj N))
    ((pullback h).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso k L N) ≪≫
      Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso h
        ((pullback k).obj L) ((pullback k).obj N))
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (h ≫ k) L N)
    ((tensor_can f g (h ≫ k) w L N).trans (Iso.trans_assoc _ _ _).symm)
    ((tensor_can h k (h ≫ k) rfl L N).trans (Iso.trans_assoc _ _ _).symm)
  exact (Iso.trans_assoc _ _ _).symm.trans (hs.trans (Iso.trans_assoc _ _ _).symm)

private theorem unit_left_eq_right (X : Scheme.{u}) :
    tensorProductLeftUnitor X.presheaf X.ringCatIsSheaf
        (SheafOfModules.unit X.ringCatSheaf) =
      tensorProductRightUnitor X.presheaf X.ringCatIsSheaf
        (SheafOfModules.unit X.ringCatSheaf) := by
  let : MonoidalCategory X.Modules :=
    Stacks.PullbackGradedAlgebra.monoidalCategory X.toRingedSpace
  exact (Stacks.SheafOfModules.Strict_leftUnitor_eq X.presheaf X.ringCatIsSheaf _).symm.trans
    ((Iso.ext (MonoidalCategory.unitors_equal (C := X.Modules))).trans
      (Stacks.SheafOfModules.Strict_rightUnitor_eq X.presheaf X.ringCatIsSheaf _))

private theorem replace_left_unit {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} {P Q U : D} (t : F.obj A ≅ P) (e : P ≅ Q) (u : F.obj B ≅ U)
    (l r : Q ≅ U) (l' r' : A ≅ B) (h : t ≪≫ e ≪≫ r = F.mapIso r' ≪≫ u)
    (h₁ : l = r) (h₂ : l' = r') : t ≪≫ e ≪≫ l = F.mapIso l' ≪≫ u := by
  simpa only [h₁, h₂] using h

/-- The original unit pullback comparison preserves the left-unitor product frame. -/
theorem pullbackUnitIso_tensorProductLeftUnitor {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
        (SheafOfModules.unit Y.ringCatSheaf) (SheafOfModules.unit Y.ringCatSheaf) ≪≫
      tensorProductIso X.presheaf X.ringCatIsSheaf (pullbackUnitIso f) (pullbackUnitIso f) ≪≫
        tensorProductLeftUnitor X.presheaf X.ringCatIsSheaf (SheafOfModules.unit X.ringCatSheaf) =
    (pullback f).mapIso (tensorProductLeftUnitor Y.presheaf Y.ringCatIsSheaf
      (SheafOfModules.unit Y.ringCatSheaf)) ≪≫ pullbackUnitIso f := by
  exact replace_left_unit (pullback f) _ _ _ _ _ _ _
    (pullbackUnitIso_tensorProductRightUnitor f) (unit_left_eq_right X) (unit_left_eq_right Y)

private theorem pullback_frame {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : D × D ⥤ D) {P Q U W V : C} {U' : D}
    (e : P ≅ U) (e' : Q ≅ U) (t : W ≅ V) (l : V ≅ U)
    (s : F.obj W ≅ T.obj (F.obj P, F.obj Q))
    (r : F.obj V ≅ T.obj (F.obj U, F.obj U)) (u : F.obj U ≅ U')
    (l' : T.obj (U', U') ≅ U')
    (hn : F.mapIso t ≪≫ r = s ≪≫ T.mapIso (Iso.prod (F.mapIso e) (F.mapIso e')))
    (hu : r ≪≫ T.mapIso (Iso.prod u u) ≪≫ l' = F.mapIso l ≪≫ u) :
    F.mapIso (t ≪≫ l) ≪≫ u =
      s ≪≫ T.mapIso (Iso.prod (F.mapIso e ≪≫ u) (F.mapIso e' ≪≫ u)) ≪≫ l' := by
  rw [← tensor_iso_trans]
  simp only [← Iso.trans_assoc] at hn ⊢
  rw [← hn]
  simp only [Iso.trans_assoc]
  rw [hu, F.mapIso_trans]
  simp only [Iso.trans_assoc]

private theorem square_frame {D : Type*} [Category D] (T : D × D ⥤ D)
    {A B C P Q R S U V : D} (x : A ≅ B) (y : B ≅ T.obj (P, Q))
    (z : A ≅ C) (v : C ≅ T.obj (R, S)) (a : P ≅ R) (b : Q ≅ S)
    (e : P ≅ U) (e' : Q ≅ U) (u : U ≅ V) (l : T.obj (V, V) ≅ V)
    (h : x ≪≫ y ≪≫ T.mapIso (Iso.prod a b) = z ≪≫ v) :
    z.symm ≪≫ x ≪≫ y ≪≫ T.mapIso (Iso.prod (e ≪≫ u) (e' ≪≫ u)) ≪≫ l =
      v ≪≫ T.mapIso (Iso.prod (a.symm ≪≫ e ≪≫ u) (b.symm ≪≫ e' ≪≫ u)) ≪≫ l := by
  have ht := tensor_iso_trans T a (a.symm ≪≫ e ≪≫ u) b (b.symm ≪≫ e' ≪≫ u)
  simp only [Iso.self_symm_id_assoc] at ht
  rw [← ht]
  simp only [← Iso.trans_assoc] at h ⊢
  rw [show ((z.symm ≪≫ x) ≪≫ y) ≪≫ T.mapIso (Iso.prod a b) = v by
    simpa [Iso.trans_assoc] using congrArg (fun t => z.symm ≪≫ t) h]

private theorem map_frame_precompose {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y Z U : C} {A B : D} (q : F.obj X ≅ A)
    (a : X ≅ Y) (b : Y ≅ Z) (c : Z ≅ U) (u : F.obj U ≅ B) :
    q.symm ≪≫ F.mapIso (a ≪≫ b ≪≫ c) ≪≫ u =
      q.symm ≪≫ F.mapIso a ≪≫ (F.mapIso (b ≪≫ c) ≪≫ u) := by
  simp only [Functor.mapIso_trans, Iso.trans_assoc]

set_option maxHeartbeats 800000 in
-- Both factors retain the actual square pullback and the original unit comparison.
/-- Pulling back the original product frame through the full-boundary square gives
exactly the product of its two original pulled-back frames. -/
theorem pullbackBoundaryTrivialization_pullbackTensorFrame {A B C D : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D) (w : f ≫ g = h ≫ k)
    (L N : D.Modules)
    (eL : (pullback g).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback g).obj N ≅ SheafOfModules.unit B.ringCatSheaf) :
    pullbackBoundaryTrivialization f g h k w
        (((Stacks.SheafOfModules.Tensor.sheafTensor D.sheaf).obj L).obj N)
        (pullbackTensorFrame g L N eL eN) =
      (pullback h).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso k L N) ≪≫
        pullbackTensorFrame h ((pullback k).obj L) ((pullback k).obj N)
          (pullbackBoundaryTrivialization f g h k w L eL)
          (pullbackBoundaryTrivialization f g h k w N eN) := by
  let T := tensorProductBifunctor A.sheaf.obj A.ringCatSheaf.property
  have hp := pullback_frame (pullback f) T eL eN
    (tensorProductIso B.sheaf.obj B.ringCatSheaf.property eL eN)
    (tensorProductLeftUnitor B.sheaf.obj B.ringCatSheaf.property
      (SheafOfModules.unit B.ringCatSheaf))
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
      ((pullback g).obj L) ((pullback g).obj N))
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
      (SheafOfModules.unit B.ringCatSheaf) (SheafOfModules.unit B.ringCatSheaf))
    (pullbackUnitIso f)
    (tensorProductLeftUnitor A.sheaf.obj A.ringCatSheaf.property
      (SheafOfModules.unit A.ringCatSheaf))
    (pullbackTensorIso_tensorProductIso f eL eN)
    (pullbackUnitIso_tensorProductLeftUnitor f)
  have hs := square_frame T
    ((pullback f).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N))
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
      ((pullback g).obj L) ((pullback g).obj N))
    (pullbackSquareIso f g h k w
      (((Stacks.SheafOfModules.Tensor.sheafTensor D.sheaf).obj L).obj N))
    ((pullback h).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso k L N) ≪≫
      Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso h
        ((pullback k).obj L) ((pullback k).obj N))
    (pullbackSquareIso f g h k w L) (pullbackSquareIso f g h k w N)
    ((pullback f).mapIso eL) ((pullback f).mapIso eN) (pullbackUnitIso f)
    (tensorProductLeftUnitor A.sheaf.obj A.ringCatSheaf.property
      (SheafOfModules.unit A.ringCatSheaf))
    (pullbackSquareIso_tensorProduct f g h k w L N)
  have hp' := congrArg (fun z =>
    (pullbackSquareIso f g h k w
      (((Stacks.SheafOfModules.Tensor.sheafTensor D.sheaf).obj L).obj N)).symm ≪≫
      (pullback f).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N) ≪≫ z) hp
  exact (map_frame_precompose (pullback f)
    (pullbackSquareIso f g h k w
      (((Stacks.SheafOfModules.Tensor.sheafTensor D.sheaf).obj L).obj N))
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g L N)
    (tensorProductIso B.sheaf.obj B.ringCatSheaf.property eL eN)
    (tensorProductLeftUnitor B.sheaf.obj B.ringCatSheaf.property
      (SheafOfModules.unit B.ringCatSheaf)) (pullbackUnitIso f)).trans
        ((hp'.trans hs).trans (Iso.trans_assoc _ _ _))

private theorem tensor_frame_naturality {D : Type*} [Category D] (T : D × D ⥤ D)
    {P Q A B C E U : D} (c : P ≅ Q) (s : P ≅ T.obj (A, B)) (t : Q ≅ T.obj (C, E))
    (a : A ≅ C) (b : B ≅ E) (e : A ≅ U) (e' : B ≅ U) (l : T.obj (U, U) ≅ U)
    (h : c ≪≫ t = s ≪≫ T.mapIso (Iso.prod a b)) :
    c.symm ≪≫ (s ≪≫ T.mapIso (Iso.prod e e') ≪≫ l) =
      t ≪≫ T.mapIso (Iso.prod (a.symm ≪≫ e) (b.symm ≪≫ e')) ≪≫ l := by
  have ht := tensor_iso_trans T a (a.symm ≪≫ e) b (b.symm ≪≫ e')
  simp only [Iso.self_symm_id_assoc] at ht
  rw [← ht]
  simp only [← Iso.trans_assoc] at h ⊢
  rw [show (c.symm ≪≫ s) ≪≫ T.mapIso (Iso.prod a b) = t by
    simpa [Iso.trans_assoc] using (congrArg (fun z => c.symm ≪≫ z) h).symm]

set_option maxHeartbeats 600000 in
-- Naturality keeps the specified product frame and both actual module comparisons.
/-- Transporting the original tensor frame by two module isomorphisms is the tensor
frame of the two transported original factor frames. -/
theorem pullbackTensorFrame_naturality {X B : Scheme.{u}} (i : B ⟶ X)
    {M N M' N' : X.Modules} (E : M ≅ M') (F : N ≅ N')
    (eM : (pullback i).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback i).obj N ≅ SheafOfModules.unit B.ringCatSheaf) :
    ((pullback i).mapIso (tensorProductIso X.sheaf.obj X.ringCatSheaf.property E F)).symm ≪≫
        pullbackTensorFrame i M N eM eN =
      pullbackTensorFrame i M' N' (((pullback i).mapIso E).symm ≪≫ eM)
        (((pullback i).mapIso F).symm ≪≫ eN) := by
  exact tensor_frame_naturality (tensorProductBifunctor B.sheaf.obj B.ringCatSheaf.property)
    ((pullback i).mapIso (tensorProductIso X.sheaf.obj X.ringCatSheaf.property E F))
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso i M N)
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso i M' N')
    ((pullback i).mapIso E) ((pullback i).mapIso F) eM eN
    (tensorProductLeftUnitor B.sheaf.obj B.ringCatSheaf.property
      (SheafOfModules.unit B.ringCatSheaf))
    (pullbackTensorIso_tensorProductIso i E F)

end AlgebraicGeometry.Scheme.Modules
