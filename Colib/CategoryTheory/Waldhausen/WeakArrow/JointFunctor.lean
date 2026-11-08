/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.WeakArrow.DualStructure
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.ReflexiveFactorization
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Functoriality
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.JointFactorization

/-!
# Actual coherent joint functors on opposite weak-arrow categories

Genuine component joint data and a coherent natural isomorphism produce an
actual joint functor on the literal opposite weak-arrow category. The
stored reversed weak square proves original weak-arrow membership. Both
component functors, every original map, and the original cofibration arrow
are retained by exact projection equalities. This owner constructs the
functor and cofibration; its exactness and coherent endpoints are proved
in separate owners.

Implementation provenance: `Quillen/Waldhausen/WeakArrow/JointFunctor.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original hypotheses, functors, component maps and independent universes are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
universe u v u' v' u'' v''
namespace CategoryTheory.Waldhausen.WeakArrow
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (W : Structure D) (Wd : Structure Dᵒᵖ) (F : C ⥤ D)
  (hW : IsCompatibleDual W Wd)

/-- A genuine weak natural arrow assembles original opposite weak-arrow objects. -/
def opFunctorOfWeakComparison {T : Type u''} [Category.{v''} T]
    (L : T ⥤ Cᵒᵖ) (R : T ⥤ Dᵒᵖ) (τ : R ⟶ L ⋙ F.op)
    (hτ : ∀ t, Wd.weq (τ.app t)) : T ⥤ (Obj W F)ᵒᵖ where
  obj t := op ⟨⟨(L.obj t).unop, (R.obj t).unop, (τ.app t).unop⟩,
    (hW.weak _).mpr (hτ t)⟩
  map {X Y} f := ((objects W F).homMk (show
      (⟨(L.obj Y).unop, (R.obj Y).unop, (τ.app Y).unop⟩ : FunctorComma.Obj F) ⟶
        ⟨(L.obj X).unop, (R.obj X).unop, (τ.app X).unop⟩ from
    ⟨(L.map f).unop, (R.map f).unop,
      (congrArg Quiver.Hom.unop (τ.naturality f)).symm⟩)).op
  map_id t := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> simp
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> simp

/-- Both projections of the assembled functor retain the given component functors. -/
@[simp] lemma opFunctorOfWeakComparison_source {T : Type u''} [Category.{v''} T]
    (L : T ⥤ Cᵒᵖ) (R : T ⥤ Dᵒᵖ) (τ : R ⟶ L ⋙ F.op)
    (hτ : ∀ t, Wd.weq (τ.app t)) :
    opFunctorOfWeakComparison W Wd F hW L R τ hτ ⋙ (source W F).op = L := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

@[simp] lemma opFunctorOfWeakComparison_target {T : Type u''} [Category.{v''} T]
    (L : T ⥤ Cᵒᵖ) (R : T ⥤ Dᵒᵖ) (τ : R ⟶ L ⋙ F.op)
    (hτ : ∀ t, Wd.weq (τ.app t)) :
    opFunctorOfWeakComparison W Wd F hW L R τ hτ ⋙ (target W F).op = R := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

variable (V : Structure C) (Vd : Structure Cᵒᵖ)
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hFd : IsExact Vd.cof Vd.weq Wd.cof Wd.weq F.op)
  (Tc : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl Vd))
  (Td : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl Wd))
  (compat : Tc.joint ⋙ ExtensionCategory.postcompose Vd Wd hFd ≅ F.op.mapArrow ⋙ Td.joint)

/-- The stored reversed weak square on each original opposite arrow. -/
def reversedArrowComparison : (target W F).op.mapArrow ⟶
    (source W F).op.mapArrow ⋙ F.op.mapArrow :=
  (Functor.mapArrowFunctor _ _).map (NatTrans.op (comparison W F))

/-- Applying the genuine component joint functor to the stored square and
then the original coherent comparison gives the endpoint/middle weak square. -/
def jointComparison : (target W F).op.mapArrow ⋙ Td.joint ⟶
    (source W F).op.mapArrow ⋙ Tc.joint ⋙ ExtensionCategory.postcompose Vd Wd hFd :=
  Functor.whiskerRight (reversedArrowComparison W F) Td.joint ≫
    Functor.whiskerLeft (source W F).op.mapArrow compat.inv

include hW in
lemma jointComparison_weak (f : Arrow (Obj W F)ᵒᵖ) :
    (ExtensionCategory.waldhausenStructure Wd).weq
      ((jointComparison W Wd F Vd hFd Tc Td compat).app f) := by
  apply (ExtensionCategory.waldhausenStructure Wd).weq.comp_mem
  · apply Td.exact.weak
    exact ⟨(hW.weak _).mp f.left.unop.property, (hW.weak _).mp f.right.unop.property⟩
  · exact (ExtensionCategory.waldhausenStructure Wd).weq_iso _ inferInstance

/-- Actual opposite endpoint-sum objects in the original weak-arrow category. -/
def jointSource : Arrow (Obj W F)ᵒᵖ ⥤ (Obj W F)ᵒᵖ :=
  opFunctorOfWeakComparison W Wd F hW
    ((source W F).op.mapArrow ⋙ Tc.joint ⋙ ExtensionCategory.source Vd)
    ((target W F).op.mapArrow ⋙ Td.joint ⋙ ExtensionCategory.source Wd)
    (Functor.whiskerRight (jointComparison W Wd F Vd hFd Tc Td compat) (ExtensionCategory.source
      Wd))
    (fun f => (jointComparison_weak W Wd F hW Vd hFd Tc Td compat f).1)

/-- Actual opposite middle objects in the original weak-arrow category. -/
def jointMiddle : Arrow (Obj W F)ᵒᵖ ⥤ (Obj W F)ᵒᵖ :=
  opFunctorOfWeakComparison W Wd F hW
    ((source W F).op.mapArrow ⋙ Tc.joint ⋙ ExtensionCategory.middle Vd)
    ((target W F).op.mapArrow ⋙ Td.joint ⋙ ExtensionCategory.middle Wd)
    (Functor.whiskerRight (jointComparison W Wd F Vd hFd Tc Td compat) (ExtensionCategory.middle
      Wd))
    (fun f => (jointComparison_weak W Wd F hW Vd hFd Tc Td compat f).2)

/-- The actual component joint arrows form a natural arrow of original
opposite weak-arrow objects. -/
def jointInclusion : jointSource W Wd F hW Vd hFd Tc Td compat ⟶
    jointMiddle W Wd F hW Vd hFd Tc Td compat where
  app f := ((objects W F).homMk (show
      ((jointMiddle W Wd F hW Vd hFd Tc Td compat).obj f).unop.obj ⟶
        ((jointSource W Wd F hW Vd hFd Tc Td compat).obj f).unop.obj from
    ⟨(Tc.joint.obj ((source W F).op.mapArrow.obj f)).obj.hom.unop,
      (Td.joint.obj ((target W F).op.mapArrow.obj f)).obj.hom.unop,
      congrArg Quiver.Hom.unop ((jointComparison W Wd F Vd hFd Tc Td compat).app f).hom.w⟩)).op
  naturality {f g} α := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact congrArg Quiver.Hom.unop (Tc.joint.map ((source W F).op.mapArrow.map α)).hom.w
    · exact congrArg Quiver.Hom.unop (Td.joint.map ((target W F).op.mapArrow.map α)).hom.w

/-- The constructed joint arrow is a genuine dual cofibration, componentwise. -/
lemma jointInclusion_cof (f : Arrow (Obj W F)ᵒᵖ) :
    (dualWaldhausenStructure V W Vd Wd F hF hFd hW).cof
      ((jointInclusion W Wd F hW Vd hFd Tc Td compat).app f) :=
  ⟨(Tc.joint.obj ((source W F).op.mapArrow.obj f)).property,
    (Td.joint.obj ((target W F).op.mapArrow.obj f)).property⟩

/-- The actual candidate joint functor into original cofibration arrows.
Its objects and maps are constructed from the two component joint functors
and their genuine coherent comparison. -/
def jointFunctor : Arrow (Obj W F)ᵒᵖ ⥤
    ExtensionCategory.Obj (dualWaldhausenStructure V W Vd Wd F hF hFd hW) where
  obj f := ⟨Arrow.mk ((jointInclusion W Wd F hW Vd hFd Tc Td compat).app f),
    jointInclusion_cof W Wd F hW V Vd hF hFd Tc Td compat f⟩
  map α := ObjectProperty.homMk (Arrow.homMk
    ((jointSource W Wd F hW Vd hFd Tc Td compat).map α)
    ((jointMiddle W Wd F hW Vd hFd Tc Td compat).map α)
    ((jointInclusion W Wd F hW Vd hFd Tc Td compat).naturality α))
  map_id f := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext <;> simp
  map_comp α β := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext <;> simp

@[simp] lemma jointFunctor_source :
    jointFunctor W Wd F hW V Vd hF hFd Tc Td compat ⋙
      ExtensionCategory.source (dualWaldhausenStructure V W Vd Wd F hF hFd hW) =
        jointSource W Wd F hW Vd hFd Tc Td compat := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

@[simp] lemma jointFunctor_middle :
    jointFunctor W Wd F hW V Vd hF hFd Tc Td compat ⋙
      ExtensionCategory.middle (dualWaldhausenStructure V W Vd Wd F hF hFd hW) =
        jointMiddle W Wd F hW Vd hFd Tc Td compat := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

/-- The source projection retains the original component joint functor,
including the actual original cofibration and every original map. -/
@[simp] lemma jointFunctor_source_component :
    jointFunctor W Wd F hW V Vd hF hFd Tc Td compat ⋙
      ExtensionCategory.postcompose (dualWaldhausenStructure V W Vd Wd F hF hFd hW) Vd
        (dual_source_exact V W Vd Wd F hF hFd hW) =
          (source W F).op.mapArrow ⋙ Tc.joint := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

/-- The target projection retains the original target component joint functor. -/
@[simp] lemma jointFunctor_target_component :
    jointFunctor W Wd F hW V Vd hF hFd Tc Td compat ⋙
      ExtensionCategory.postcompose (dualWaldhausenStructure V W Vd Wd F hF hFd hW) Wd
        (dual_target_exact V W Vd Wd F hF hFd hW) =
          (target W F).op.mapArrow ⋙ Td.joint := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

end CategoryTheory.Waldhausen.WeakArrow
