/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliarySupportNull
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullCurrentNull

/-!
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliaryBasicNull.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The original auxiliary null and basic full-open null at the same time

The original weak-change and geometric open-restriction Model arrows factor the
same fixed-factor product pullback. The actual auxiliary composite-forget square
therefore compares its selected-zero null with the original basic full-open null.
Both the source-zero transport and the restriction postcomposition are retained;
the equality holds before any telescope or normalized presentation is introduced.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport

private theorem zero_postcomp {V W U : WideSubcategory preservesZero.{u}} (J : W ⟶ U) :
    zeroHom V U = zeroHom V W ≫ J := by
  simpa only [Category.id_comp] using (zeroHom_square (𝟙 V) J).symm

private def zeroPostcomp {V W U : WideSubcategory preservesZero.{u}}
    (F : V ⟶ W) (J : W ⟶ U)
    (η : (zeroHom V W).hom.toFunctor ⟶ F.hom.toFunctor) :
    (zeroHom V U).hom.toFunctor ⟶ (F ≫ J).hom.toFunctor :=
  eqToHom (congrArg (fun k : V ⟶ U ↦ k.hom.toFunctor) (zero_postcomp (V := V) J)) ≫
    Functor.whiskerRight η J.hom.toFunctor

private theorem zeroPostcomp_weak {V W U : WideSubcategory preservesZero.{u}}
    (F : V ⟶ W) (J : W ⟶ U)
    (η : (zeroHom V W).hom.toFunctor ⟶ F.hom.toFunctor)
    (hη : ∀ X, W.obj.waldhausen.weq (η.app X)) (X : V.obj.Obj) :
    U.obj.waldhausen.weq ((zeroPostcomp F J η).app X) := by
  apply U.obj.waldhausen.weq.comp_mem
  · exact U.obj.waldhausen.weq_iso _ (by infer_instance)
  · exact J.hom.isExact.weak _ (hη X)

private theorem zeroPostcomp_level {V W U : WideSubcategory preservesZero.{u}}
    (F : V ⟶ W) (J : W ⟶ U)
    (η : (zeroHom V W).hom.toFunctor ⟶ F.hom.toFunctor)
    (hη : ∀ X, W.obj.waldhausen.weq (η.app X)) (n : ℕ) :
    (prespectrumTransformationHomotopy (F := zeroHom V U) (G := F ≫ J)
      (zeroPostcomp F J η)
      (zeroPostcomp_weak F J η hη)).level n =
      ((prespectrumTransformationHomotopy (F := zeroHom V W) (G := F) η hη).postcomp
        (prespectrumMap J)).level n :=
  (prespectrumTransformationHomotopy_source_transport_level
    (F := zeroHom V U) (F' := zeroHom V W ≫ J) (G := F ≫ J) (zero_postcomp J)
    (Functor.whiskerRight η J.hom.toFunctor) (fun X => J.hom.isExact.weak _ (hη X))
    (zeroPostcomp_weak F J η hη) n).trans
      (prespectrumTransformationHomotopy_postcomp_level (F := zeroHom V W) (G := F) η hη J n)

private theorem fullNull_postcomp_naturality {V W U V' W' T' U' : WideSubcategory preservesZero.{u}}
    (f : V ⟶ W) (g : W ⟶ U)
    (f' : V' ⟶ W') (g' : W' ⟶ T') (J' : T' ⟶ U')
    (a : V ⟶ V') (b : U ⟶ U')
    (h : (f ≫ g) ≫ b = a ≫ ((f' ≫ g') ≫ J'))
    (η : (zeroHom V U).hom.toFunctor ⟶ (f ≫ g).hom.toFunctor)
    (η' : (zeroHom V' T').hom.toFunctor ⟶ (f' ≫ g').hom.toFunctor)
    (hη : ∀ X, U.obj.waldhausen.weq (η.app X))
    (hη' : ∀ X, T'.obj.waldhausen.weq (η'.app X))
    (n : ℕ) (s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumMap b).map n
      ((prespectrumCompositeZeroNullHomotopy f g η hη).level n (s, x)) =
    (prespectrumMap J').map n
      ((prespectrumCompositeZeroNullHomotopy f' g' η' hη').level n
        (s, (prespectrumMap a).map n x)) := by
  have hn := prespectrumZeroTransformationHomotopy_naturality
    (f ≫ g) ((f' ≫ g') ≫ J') a b h η (zeroPostcomp (f' ≫ g') J' η')
    hη (zeroPostcomp_weak (f' ≫ g') J' η' hη') n
  have hv := congrArg (fun H => H (unitInterval.symm s, x)) hn
  change (prespectrumMap b).map n
    ((prespectrumTransformationHomotopy _ _).level n (unitInterval.symm s, x)) =
      (prespectrumTransformationHomotopy _ _).level n
        (unitInterval.symm s, (prespectrumMap a).map n x) at hv
  rw [zeroPostcomp_level] at hv
  exact hv

variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- Actual weak change followed by open restriction is the original product pullback. -/
theorem fullRestriction_eq_ambientMap :
    ParameterModels.changeWeak f ≫ ParameterModels.openRestriction f = ambientMap f := by
  unfold ParameterModels.changeWeak ParameterModels.openRestriction
  rw [← Functor.whiskerLeft_comp, pairOpen_factor]
  rfl

/-- The actual auxiliary composite and basic full restriction have the same Model square. -/
theorem fullComposite_basic_square :
    (enlargement f T ≫ restriction f T) ≫ ParameterModels.forget (inverseOpen f T).ι =
      toBasic f T ≫ ((ParameterModels.forget f ≫ ParameterModels.changeWeak f) ≫
        ParameterModels.openRestriction f) := by
  rw [Category.assoc (ParameterModels.forget f), fullRestriction_eq_ambientMap]
  exact composite_forget f T

/-- Forgetting auxiliary support preserves the original full-open null at every unchanged time. -/
theorem fullNull_basic_square (X : Scheme.{u}ᵒᵖ) (n : ℕ) (s : unitInterval)
    (x : (prespectrum ((fiber f T).obj X)).space n) :
    (prespectrumMap ((ParameterModels.forget (inverseOpen f T).ι).app X)).map n
      (((fullNull f T).homotopy X).level n (s, x)) =
      ((ParameterFullCurrentNull.fullNull f).homotopy X).level n
        (s, (prespectrumMap ((toBasic f T).app X)).map n x) := by
  apply fullNull_postcomp_naturality
    ((enlargement f T).app X) ((restriction f T).app X)
    ((ParameterModels.forget f).app X) ((ParameterModels.changeWeak f).app X)
    ((ParameterModels.openRestriction f).app X) ((toBasic f T).app X)
    ((ParameterModels.forget (inverseOpen f T).ι).app X)
  exact NatTrans.congr_app (fullComposite_basic_square f T) X

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
