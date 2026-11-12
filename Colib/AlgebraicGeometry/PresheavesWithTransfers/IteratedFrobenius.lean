/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RadicialComponents
public import Colib.AlgebraicGeometry.Sites.Smooth.IteratedFrobenius
public import Colib.AlgebraicGeometry.Morphisms.Frobenius.SeparablePoint

/-!
# Actual iterated Frobenius transfer isomorphisms and closed-point reduction

The native n-fold relative Frobenius is a finite flat universal homeomorphism between the
original smooth objects. Its actual graph pullback is therefore inverted by the genuine
componentwise transfers. For each original closed point, finitely many such iterations
produce an actual closed point with separable residue field and invertible original pullback.
This does not assert counit compatibility or a field-change equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Frobenius

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)

/-- Invert the graph of the literal native iterated relative Frobenius on all smooth objects. -/
@[colib_tag "COL-1106"]
def nFoldRelativeFrobeniusIso (p : ℕ) [Fact p.Prime]
    (hk : IsInCharacteristic (Spec (.of k)) p) (m : ℕ)
    (X : SmoothSite (Spec (.of k))) (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ)) :
    sections P (Cor.mk (SmoothSite.nFoldFrobeniusTwist p hk m X)) ≅
      sections P (Cor.mk X) :=
  radicialGraphIsoOfComponents P (SmoothSite.nFoldRelativeFrobenius p hk m X) n hn hP

@[simp]
theorem nFoldRelativeFrobeniusIso_hom (p : ℕ) [Fact p.Prime]
    (hk : IsInCharacteristic (Spec (.of k)) p) (m : ℕ)
    (X : SmoothSite (Spec (.of k))) (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ)) :
    (nFoldRelativeFrobeniusIso P p hk m X n hn hP).hom =
      ((toPresheaf k).obj P).map (SmoothSite.nFoldRelativeFrobenius p hk m X).op := rfl

/-- The original closed point acquires separable residue field at its native Frobenius image,
while the original presheaf restriction along that exact native map is an isomorphism. -/
@[colib_tag "COL-1106"]
theorem exists_separable_closedPoint_iteratedFrobenius_iso
    (p : ℕ) [Fact p.Prime] [CharP k p] (X : SmoothSite (Spec (.of k)))
    (x : X.left) (hx : IsClosed ({x} : Set X.left)) (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ)) :
    ∃ m : ℕ,
      let T := SmoothSite.nFoldFrobeniusTwist p (isInCharacteristic_spec k p) m X
      let q : X ⟶ T := SmoothSite.nFoldRelativeFrobenius p (isInCharacteristic_spec k p) m X
      letI : Algebra k (T.left.residueField (q.left x)) :=
        (fieldToResidue T.hom (q.left x)).hom.toAlgebra
      IsClosed ({q.left x} : Set T.left) ∧
        Algebra.IsSeparable k (T.left.residueField (q.left x)) ∧
        IsIso (((toPresheaf k).obj P).map q.op) := by
  obtain ⟨m, hm⟩ := exists_isClosed_isSeparable_nFoldRelativeFrobenius_image p X.hom x hx
  refine ⟨m, hm.1, hm.2, ?_⟩
  exact (nFoldRelativeFrobeniusIso P p (isInCharacteristic_spec k p) m X n hn hP).isIso_hom

/-- The native n-fold graph pullbacks are a natural isomorphism of the original presheaf. -/
@[colib_tag "COL-1106", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/FrobeniusDescent.lean:70-104"
  "ingredient" "Only original n-fold Frobenius naturality; the transfer inverse is proved here."]
def nFoldRelativeFrobeniusPresheafIso (p : ℕ) [Fact p.Prime]
    (hk : IsInCharacteristic (Spec (.of k)) p) (m : ℕ) (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ)) :
    (SmoothSite.nFoldFrobeniusTwistFunctor p hk m).op ⋙ (toPresheaf k).obj P ≅
      (toPresheaf k).obj P := by
  refine NatIso.ofComponents
    (fun X => nFoldRelativeFrobeniusIso P p hk m X.unop n hn hP) ?_
  intro X Y f
  let F := (toPresheaf k).obj P
  let T := SmoothSite.nFoldFrobeniusTwistFunctor p hk m
  let η : 𝟭 _ ⟶ T := SmoothSite.nFoldRelativeFrobeniusNatTrans p hk m
  change F.map (T.map f.unop).op ≫ F.map (η.app Y.unop).op =
    F.map (η.app X.unop).op ≫ F.map f
  rw [← F.map_comp, ← F.map_comp]
  exact congrArg (fun a : Y.unop ⟶ T.obj X.unop => F.map a.op)
    (η.naturality f.unop).symm

@[simp]
theorem nFoldRelativeFrobeniusPresheafIso_hom_app (p : ℕ) [Fact p.Prime]
    (hk : IsInCharacteristic (Spec (.of k)) p) (m : ℕ) (n : ℕ) (hn : IsUnit (n : k))
    (hP : ∀ W : SmoothSite (Spec (.of k)),
      Module.IsTorsionBy ℤ (sections P (Cor.mk W)) (n : ℤ))
    (X : (SmoothSite (Spec (.of k)))ᵒᵖ) :
    (nFoldRelativeFrobeniusPresheafIso P p hk m n hn hP).hom.app X =
      ((toPresheaf k).obj P).map (SmoothSite.nFoldRelativeFrobenius p hk m X.unop).op := rfl

end AlgebraicGeometry.PresheafWithTransfers
