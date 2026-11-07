/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.Waldhausen.CanonicalMap
public import Colib.KTheory.Waldhausen.GrothendieckComparison.WeakObjectCompositionTrack
public import Colib.KTheory.Waldhausen.GrothendieckComparison.WeakObjectNaturality
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.KOneNormalization

/-! # Original weak-endomorphism and automorphism classes in homotopical K-one -/

/-! Implementation provenance: selected declarations from
`Quillen/Waldhausen/AutomorphismKOne.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original weak-arrow paths,
composition order, object-component transport, and canonical chosen-zero rebasing
are retained. Fundamental-group classes use native `FundamentalGroup.fromPath`,
and the native `Aut` structure supplies its underlying isomorphism through `asIso`.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite Convexity Topology
open scoped Simplicial Topology
universe u v

namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The original weak-arrow loop, normalized from its actual object component into K-one. -/
def weakEndomorphismKOneClass {A : C} (f : A ⟶ A) (hf : W.weq f) : W.K 1 :=
  Topology.loopKOneNormalization (W.kZeroObjectLoop A)
    (FundamentalGroup.fromPath ⟦W.weakObjectSquareLoopPath f hf⟧)

/-- Equality of original endomorphisms gives equality of their normalized classes. -/
theorem weakEndomorphismKOneClass_congr {A : C} {f g : A ⟶ A}
    (h : f = g) (hf : W.weq f) (hg : W.weq g) :
    W.weakEndomorphismKOneClass f hf = W.weakEndomorphismKOneClass g hg := by
  subst g
  rfl

/-- An actual automorphism supplies its own original fine weak-arrow K-one class. -/
def automorphismKOneClass {A : C} (e : A ≅ A) : W.K 1 :=
  W.weakEndomorphismKOneClass e.hom (W.weq_iso e.hom inferInstance)

/-- The identity automorphism represents the identity element of the original K-one group. -/
theorem automorphismKOneClass_refl (A : C) : W.automorphismKOneClass (Iso.refl A) = 1 := by
  change Topology.loopKOneNormalization (W.kZeroObjectLoop A)
    (FundamentalGroup.fromPath ⟦W.weakObjectSquareLoopPath (𝟙 A) (W.weq.id_mem A)⟧ :
      FundamentalGroup _ (W.kZeroObjectLoop A)) = 1
  rw [weakObjectSquareLoopPath_id]
  exact (Topology.loopKOneNormalization (W.kZeroObjectLoop A)).map_one

/-- Composition follows the original weak-arrow triangle and the fundamental-group convention. -/
theorem weakEndomorphismKOneClass_comp {A : C} (f g : A ⟶ A)
    (hf : W.weq f) (hg : W.weq g) :
    W.weakEndomorphismKOneClass (f ≫ g) (W.weq.comp_mem _ _ hf hg) =
      W.weakEndomorphismKOneClass g hg * W.weakEndomorphismKOneClass f hf := by
  have he : (FundamentalGroup.fromPath
      ⟦W.weakObjectSquareLoopPath (f ≫ g) (W.weq.comp_mem _ _ hf hg)⟧ :
      FundamentalGroup _ (W.kZeroObjectLoop A)) =
      FundamentalGroup.fromPath
        ⟦(W.weakObjectSquareLoopPath f hf).trans (W.weakObjectSquareLoopPath g hg)⟧ := by
    apply End.ext
    exact Quotient.sound ⟨(W.weakObjectSquareCompositionTrack f g hf hg).symm⟩
  let a : FundamentalGroup (Path W.kBasepoint W.kBasepoint) (W.kZeroObjectLoop A) :=
    FundamentalGroup.fromPath ⟦W.weakObjectSquareLoopPath f hf⟧
  let b : FundamentalGroup (Path W.kBasepoint W.kBasepoint) (W.kZeroObjectLoop A) :=
    FundamentalGroup.fromPath ⟦W.weakObjectSquareLoopPath g hg⟧
  have hab : b * a =
      FundamentalGroup.fromPath
        ⟦(W.weakObjectSquareLoopPath f hf).trans (W.weakObjectSquareLoopPath g hg)⟧ := rfl
  change Topology.loopKOneNormalization (W.kZeroObjectLoop A) _ =
    Topology.loopKOneNormalization (W.kZeroObjectLoop A) b *
      Topology.loopKOneNormalization (W.kZeroObjectLoop A) a
  rw [he, ← hab]
  exact (Topology.loopKOneNormalization (W.kZeroObjectLoop A)).map_mul b a

/-- Actual automorphisms act by their original weak-arrow classes in K-one. -/
def automorphismKOneHom (A : C) : Aut A →* W.K 1 where
  toFun e := W.automorphismKOneClass e.asIso
  map_one' := W.automorphismKOneClass_refl A
  map_mul' e f := W.weakEndomorphismKOneClass_comp f.asIso.hom e.asIso.hom
    (W.weq_iso _ inferInstance) (W.weq_iso _ inferInstance)

/-- The original class is invariant under a specified weak-arrow intertwining isomorphism. -/
theorem weakEndomorphismKOneClass_iso {A B : C} (e : A ≅ B)
    (f : A ⟶ A) (g : B ⟶ B) (hf : W.weq f) (hg : W.weq g)
    (h : f ≫ e.hom = e.hom ≫ g) :
    W.weakEndomorphismKOneClass f hf = W.weakEndomorphismKOneClass g hg := by
  let he := W.weq_iso e.hom inferInstance
  let p := W.weakObjectSquareLoopPath e.hom he
  let α := W.weakObjectSquareLoopPath f hf
  let β := W.weakObjectSquareLoopPath g hg
  have H : (α.trans p).Homotopy (p.trans β) :=
    (W.weakObjectSquareCompositionTrack f e.hom hf he).trans
      (((W.weakObjectSquareCompositionTrack e.hom g he hg).symm).cast
        (W.weakObjectSquareLoopPath_congr h.symm _ _) rfl)
  let ca : FundamentalGroupoid (Path W.kBasepoint W.kBasepoint) :=
    FundamentalGroupoid.mk (W.kZeroObjectLoop A)
  let cb : FundamentalGroupoid (Path W.kBasepoint W.kBasepoint) :=
    FundamentalGroupoid.mk (W.kZeroObjectLoop B)
  let c : ca ⟶ cb := ⟦p⟧
  let aa : ca ⟶ ca := ⟦α⟧
  let bb : cb ⟶ cb := ⟦β⟧
  have ht : aa ≫ c = c ≫ bb := by
    change (⟦α.trans p⟧ : Path.Homotopic.Quotient _ _) = ⟦p.trans β⟧
    exact Quotient.sound ⟨H⟩
  have hp : FundamentalGroup.fundamentalGroupMulEquivOfPath p
      (FundamentalGroup.fromPath ⟦α⟧) = FundamentalGroup.fromPath ⟦β⟧ := by
    apply End.ext
    change Groupoid.inv c ≫ aa ≫ c = bb
    rw [ht]
    simp
  change Topology.loopKOneNormalization (W.kZeroObjectLoop A) (FundamentalGroup.fromPath ⟦α⟧) =
    Topology.loopKOneNormalization (W.kZeroObjectLoop B) (FundamentalGroup.fromPath ⟦β⟧)
  rw [← Topology.loopKOneNormalization_transport p, hp]

attribute [colib_tag "COL-0299"] weakEndomorphismKOneClass_comp

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/AutomorphismKOne.lean:61-78" "adaptation"
  "The actual composition track gives class(f ≫ g) = class(g) * class(f); native fundamental-
    group End wrappers preserve the original order"]
  weakEndomorphismKOneClass_comp

attribute [colib_tag "COL-0299"] automorphismKOneHom

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/AutomorphismKOne.lean:81-85" "adaptation"
  "The native Aut A monoid homomorphism uses the original automorphism class through
    Aut.asIso and the original reversed composition convention"]
  automorphismKOneHom

end CategoryTheory.Waldhausen.Structure

namespace CategoryTheory.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D} {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- A strict zero equality gives naturality through the original unmodified realization map. -/
theorem KMap_weakEndomorphismKOneClass_of_zeroEq (h0 : F.obj V.zero = W.zero)
    {A : C} (f : A ⟶ A) (hf : V.weq f) :
    KMap hF 1 (V.weakEndomorphismKOneClass f hf) =
      W.weakEndomorphismKOneClass (F.map f) (hF.weak f hf) := by
  rw [KMap_eq_piMap_of_zeroEq hF h0 1]
  unfold Structure.weakEndomorphismKOneClass
  rw [Topology.loopKOneNormalization_naturality_of_loopEq (deloopingMap hF).hom
    (deloopingMap_basepoint_of_zeroEq hF h0) (V.kZeroObjectLoop A)
    (W.kZeroObjectLoop (F.obj A)) (objectLoopMapEq hF h0 A)]
  rw [weakObjectSquareLoopPath_postcompose hF h0 f hf]

/-- Every original K-map preserves the independently defined weak-endomorphism class.
The proof retains its canonical chosen-zero rebase and the actual object isomorphism. -/
theorem KMap_weakEndomorphismKOneClass {A : C} (f : A ⟶ A) (hf : V.weq f) :
    KMap hF 1 (V.weakEndomorphismKOneClass f hf) =
      W.weakEndomorphismKOneClass (F.map f) (hF.weak f hf) := by
  let e := rebaseFunctorIso F V.zero W.zero ((hF.zero V.isZero).iso W.isZero)
  have hn := KMap_weakEndomorphismKOneClass_of_zeroEq hF.rebase
    (rebaseFunctor_obj_base _ _ _ _) f hf
  rw [KMap_eq_piMap_of_zeroEq hF.rebase (rebaseFunctor_obj_base _ _ _ _) 1] at hn
  rw [KMap_eq_piMap]
  exact hn.trans (W.weakEndomorphismKOneClass_iso (e.app A) (F.map f) _
    (hF.weak f hf) (hF.rebase.weak f hf) (e.hom.naturality f)).symm

/-- The intrinsic automorphism class is natural for the original canonically based K-map. -/
theorem KMap_automorphismKOneClass {A : C} (e : A ≅ A) :
    KMap hF 1 (V.automorphismKOneClass e) = W.automorphismKOneClass (F.mapIso e) :=
  KMap_weakEndomorphismKOneClass hF e.hom (V.weq_iso _ inferInstance)

attribute [colib_tag "COL-0299"] KMap_weakEndomorphismKOneClass

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/AutomorphismKOne.lean:225-234" "adaptation"
  "The original canonical KMap preserves weak-endomorphism classes using rebaseFunctorIso and
    actual intertwining-isomorphism invariance, without strict chosen-zero preservation"]
  KMap_weakEndomorphismKOneClass

attribute [colib_tag "COL-0299"] KMap_automorphismKOneClass

attribute [colib_ref "quillen"
  "Quillen/Waldhausen/AutomorphismKOne.lean:237-239" "adaptation"
  "The original canonical KMap preserves the independently defined automorphism class for
    exact functors in the original common universe range, without a strict chosen-zero
    hypothesis"]
  KMap_automorphismKOneClass

end CategoryTheory.Waldhausen
