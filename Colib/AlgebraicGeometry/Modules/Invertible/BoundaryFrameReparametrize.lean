/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Modules.Invertible.PullbackTensorFrameComparison
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.Limits.BoundaryScalarPullback

/-! # Boundary reparametrization with unchanged ambient modules and sections

The frame uses the literal named-composite comparison. In particular the ambient
module is not replaced by its pullback along an identity morphism. The private
categorical tensor manipulations specialize those in PullbackTensorFrameComparison.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
open Stacks.AlgebraicGeometry.ModuleLimits Stacks.SheafOfModules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Transport a full-boundary frame along the prescribed reparametrization. -/
def boundaryFrameReparametrize {A B X : Scheme.{u}}
    (u : A ⟶ B) (g : B ⟶ X) (h : A ⟶ X) (w : u ≫ g = h)
    (M : X.Modules) (e : (pullback g).obj M ≅ SheafOfModules.unit B.ringCatSheaf) :
    (pullback h).obj M ≅ SheafOfModules.unit A.ringCatSheaf :=
  (canIso u g h w M).symm ≪≫ (pullback u).mapIso e ≪≫ pullbackUnitIso u

/-- The same actual ambient global section stays normalized on the entire boundary. -/
theorem boundaryFrameReparametrize_section_one {A B X : Scheme.{u}}
    (u : A ⟶ B) (g : B ⟶ X) (h : A ⟶ X) (w : u ≫ g = h)
    (M : X.Modules) (e : (pullback g).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (a : Γ(M, ⊤))
    (ha : Hom.app e.hom ⊤ (pullbackGlobalSections g M a) = (1 : Γ(B, ⊤))) :
    Hom.app (boundaryFrameReparametrize u g h w M e).hom ⊤
      (pullbackGlobalSections h M a) = (1 : Γ(A, ⊤)) := by
  have hp := canIso_pullbackGlobalSections u g h w M a
  have hi := (congrArg (Hom.app (canIso u g h w M).inv ⊤) hp).symm.trans
    (app_inv_app (canIso u g h w M) ⊤ _)
  change Hom.app (pullbackUnitIso u).hom ⊤
    (Hom.app ((pullback u).map e.hom) ⊤
      (Hom.app (canIso u g h w M).inv ⊤ (pullbackGlobalSections h M a))) = _
  rw [hi]
  have hn := Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality
    u e.hom (pullbackGlobalSections g M a)
  exact (congrArg (Hom.app (pullbackUnitIso u).hom ⊤) hn.symm).trans
    ((congrArg (fun z => Hom.app (pullbackUnitIso u).hom ⊤
      (pullbackGlobalSections u (SheafOfModules.unit B.ringCatSheaf) z)) ha).trans
        ((SectionsEqualizer.pullbackUnitIso_unit u (1 : Γ(B, ⊤))).trans (map_one u.appTop.hom)))

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

/-- The original product frame reparametrizes to the product of the two original
reparametrized frames. Both ambient modules are unchanged. -/
theorem boundaryFrameReparametrize_tensorFrame {A B X : Scheme.{u}}
    (u : A ⟶ B) (g : B ⟶ X) (h : A ⟶ X) (w : u ≫ g = h)
    (M N : X.Modules)
    (eM : (pullback g).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback g).obj N ≅ SheafOfModules.unit B.ringCatSheaf) :
    boundaryFrameReparametrize u g h w
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N)
      (pullbackTensorFrame g M N eM eN) =
    pullbackTensorFrame h M N
      (boundaryFrameReparametrize u g h w M eM)
      (boundaryFrameReparametrize u g h w N eN) := by
  let T := tensorProductBifunctor A.sheaf.obj A.ringCatSheaf.property
  have hp := pullback_frame (pullback u) T eM eN
    (tensorProductIso B.sheaf.obj B.ringCatSheaf.property eM eN)
    (tensorProductLeftUnitor B.sheaf.obj B.ringCatSheaf.property
      (SheafOfModules.unit B.ringCatSheaf))
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso u
      ((pullback g).obj M) ((pullback g).obj N))
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso u
      (SheafOfModules.unit B.ringCatSheaf) (SheafOfModules.unit B.ringCatSheaf))
    (pullbackUnitIso u)
    (tensorProductLeftUnitor A.sheaf.obj A.ringCatSheaf.property
      (SheafOfModules.unit A.ringCatSheaf))
    (pullbackTensorIso_tensorProductIso u eM eN)
    (pullbackUnitIso_tensorProductLeftUnitor u)
  have hs := square_frame T
    ((pullback u).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g M N))
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso u
      ((pullback g).obj M) ((pullback g).obj N))
    (canIso u g h w (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N))
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso h M N)
    (canIso u g h w M) (canIso u g h w N)
    ((pullback u).mapIso eM) ((pullback u).mapIso eN) (pullbackUnitIso u)
    (tensorProductLeftUnitor A.sheaf.obj A.ringCatSheaf.property
      (SheafOfModules.unit A.ringCatSheaf))
    (tensor_can u g h w M N).symm
  have hp' := congrArg (fun z =>
    (canIso u g h w (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N)).symm ≪≫
      (pullback u).mapIso (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g M N) ≪≫ z) hp
  exact (map_frame_precompose (pullback u)
    (canIso u g h w (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N))
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g M N)
    (tensorProductIso B.sheaf.obj B.ringCatSheaf.property eM eN)
    (tensorProductLeftUnitor B.sheaf.obj B.ringCatSheaf.property
      (SheafOfModules.unit B.ringCatSheaf)) (pullbackUnitIso u)).trans
      (hp'.trans hs)

/-- Both auxiliary boundary-one equations transport without changing their original
ambient modules or sections. -/
theorem boundaryFrameReparametrize_pair_one {A B X : Scheme.{u}}
    (u : A ⟶ B) (g : B ⟶ X) (h : A ⟶ X) (w : u ≫ g = h)
    (M N : X.Modules)
    (eM : (pullback g).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (eN : (pullback g).obj N ≅ SheafOfModules.unit B.ringCatSheaf)
    (a : Γ(((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj M).obj N, ⊤))
    (b : Γ(N, ⊤))
    (ha : Hom.app (pullbackTensorFrame g M N eM eN).hom ⊤
      (pullbackGlobalSections g _ a) = (1 : Γ(B, ⊤)))
    (hb : Hom.app eN.hom ⊤ (pullbackGlobalSections g N b) = (1 : Γ(B, ⊤))) :
    Hom.app (pullbackTensorFrame h M N
      (boundaryFrameReparametrize u g h w M eM)
      (boundaryFrameReparametrize u g h w N eN)).hom ⊤
      (pullbackGlobalSections h _ a) = (1 : Γ(A, ⊤)) ∧
    Hom.app (boundaryFrameReparametrize u g h w N eN).hom ⊤
      (pullbackGlobalSections h N b) = (1 : Γ(A, ⊤)) := by
  constructor
  · rw [← boundaryFrameReparametrize_tensorFrame]
    exact boundaryFrameReparametrize_section_one u g h w _ _ a ha
  · exact boundaryFrameReparametrize_section_one u g h w N eN b hb

end AlgebraicGeometry.Scheme.Modules
