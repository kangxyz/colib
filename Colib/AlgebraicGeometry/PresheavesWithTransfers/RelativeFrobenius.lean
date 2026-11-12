/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RadicialTorsion
public import Colib.AlgebraicGeometry.Sites.Smooth.Frobenius

/-!
# Relative Frobenius on the original prime-to-characteristic torsion sections

The source, twist and map are the actual original smooth-site constructions. Native geometry
supplies finiteness, flatness, universal injectivity and integrality of the twist. The proved
radicial torsion consumer therefore applies directly, with its explicit full-degree Bezout
transfer inverse. This is an objectwise Frobenius isomorphism, not a field-change equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Stacks.Frobenius

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] (P : PresheafWithTransfers.{v} k)
  (p : ℕ) [Fact p.Prime] [CharP k p] (X : Scheme.SmoothSite (Spec (.of k)))
  [IsIntegral X.left]

/-- The original relative Frobenius pullback is an actual isomorphism on prime-to-characteristic
 torsion sections, with all geometry supplied from the original smooth-site source. -/
@[colib_tag "COL-1098"]
def relativeFrobeniusIso (n : ℕ) (hn : IsUnit (n : k))
    (hX : Module.IsTorsionBy ℤ (sections P (Cor.mk X)) (n : ℤ))
    (hT : Module.IsTorsionBy ℤ
      (sections P (Cor.mk (Scheme.SmoothSite.frobeniusTwist p (isInCharacteristic_spec k p) X)))
      (n : ℤ)) :
    sections P (Cor.mk (Scheme.SmoothSite.frobeniusTwist p (isInCharacteristic_spec k p) X)) ≅
      sections P (Cor.mk X) :=
  radicialGraphIso P (Scheme.SmoothSite.relativeFrobenius p (isInCharacteristic_spec k p) X)
    n hn hX hT

/-- The hom is the original ordinary presheaf restriction, not a replacement map. -/
@[simp]
theorem relativeFrobeniusIso_hom (n : ℕ) (hn : IsUnit (n : k))
    (hX : Module.IsTorsionBy ℤ (sections P (Cor.mk X)) (n : ℤ))
    (hT : Module.IsTorsionBy ℤ
      (sections P (Cor.mk (Scheme.SmoothSite.frobeniusTwist p (isInCharacteristic_spec k p) X)))
      (n : ℤ)) :
    (relativeFrobeniusIso P p X n hn hX hT).hom =
      ((toPresheaf k).obj P).map
        (Scheme.SmoothSite.relativeFrobenius p (isInCharacteristic_spec k p) X).op := rfl

/-- The inverse is the explicit full-degree Bezout multiple of the original transpose transfer. -/
@[simp]
theorem relativeFrobeniusIso_inv (n : ℕ) (hn : IsUnit (n : k))
    (hX : Module.IsTorsionBy ℤ (sections P (Cor.mk X)) (n : ℤ))
    (hT : Module.IsTorsionBy ℤ
      (sections P (Cor.mk (Scheme.SmoothSite.frobeniusTwist p (isInCharacteristic_spec k p) X)))
      (n : ℤ)) :
    (relativeFrobeniusIso P p X n hn hX hT).inv =
      Nat.gcdA
        ((Scheme.SmoothSite.relativeFrobenius p (isInCharacteristic_spec k p) X).left.residueDegree
          (genericPoint X.left)) n •
        transfer P (Cor.finiteFlatTranspose k
          (Scheme.SmoothSite.relativeFrobenius p (isInCharacteristic_spec k p) X)) := rfl

/-- The actual original relative Frobenius restriction is an isomorphism. -/
@[colib_tag "COL-1098"]
theorem isIso_toPresheaf_map_relativeFrobenius (n : ℕ) (hn : IsUnit (n : k))
    (hX : Module.IsTorsionBy ℤ (sections P (Cor.mk X)) (n : ℤ))
    (hT : Module.IsTorsionBy ℤ
      (sections P (Cor.mk (Scheme.SmoothSite.frobeniusTwist p (isInCharacteristic_spec k p) X)))
      (n : ℤ)) :
    IsIso (((toPresheaf k).obj P).map
      (Scheme.SmoothSite.relativeFrobenius p (isInCharacteristic_spec k p) X).op) :=
  (relativeFrobeniusIso P p X n hn hX hT).isIso_hom

end AlgebraicGeometry.PresheafWithTransfers
