/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.AffineLineMotivicRepresentative
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.Cofiber
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.Collapse

import Colib.CategoryTheory.Sites.Simplicial.ReducedCofiberExact

/-!
# Reduced motivic cohomology of the two Tate collapse squares

The affine-line collapse gives a short exact sequence of the actual
reduced cochains. The pointed line is contractible in A¹-localization,
so precomposition by the quotient map is bijective in reduced motivic
cohomology. The original Tate quotient has a second short exact
sequence, whose connecting map gives the suspension comparison.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Pretriangulated Limits Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.PresheafWithTransfers
open CategoryTheory.PointedSimplicialPresheaf

universe d u

namespace AlgebraicGeometry.MotivicHomotopy

private theorem bijective_precomp_mor₂_of_subsingleton
    {D : Type*} [Category* D] [Preadditive D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [HasZeroObject D] [Pretriangulated D] (T : Triangle D) (hT : T ∈ distTriang D) (V : D)
    (h : Subsingleton (T.obj₁ ⟶ V)) (h' : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ V)) :
    Function.Bijective (fun a : T.obj₃ ⟶ V => T.mor₂ ≫ a) := by
  constructor
  · intro x y hxy
    change T.mor₂ ≫ x = T.mor₂ ≫ y at hxy
    apply sub_eq_zero.mp
    have hz : T.mor₂ ≫ (x - y) = 0 := by rw [Preadditive.comp_sub, hxy, sub_self]
    obtain ⟨g, hg⟩ := T.yoneda_exact₃ hT (x - y) hz
    exact hg.trans (by rw [h'.elim g 0, comp_zero])
  · intro y
    obtain ⟨g, hg⟩ := T.yoneda_exact₂ hT y (h.elim _ _)
    exact ⟨g, hg.symm⟩

section Motivic

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{d}
    (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "R" => CommRingCat.of k
local notation "S" => Spec (CommRingCat.of k)
local notation "C" => SmoothSite (Spec (CommRingCat.of k))
local notation "J" => nisnevichTopology (Spec (CommRingCat.of k))
local notation "X" => liftedPointedAffineLine (CommRingCat.of k)

private theorem subsingleton_reducedMotivicHomFromPointedAffineLine (n : ℤ) (q : ℕ) :
    Subsingleton ((reducedDerivedChains.{d, u + 1} C J).obj X ⟶
      (DerivedCategory.Q.obj (motivicSheafComplex k q))⟦n⟧) := by
  let Q := toAffineLineHomotopyCategory S
  let P := point.{u + 1} C
  let E := motivicAffineLineRepresentativeHomEquiv.{d} k n q
  let : IsIso (Q.map (toPoint C X)) :=
    isIso_toAffineLineHomotopyCategory_map_pointedAffineLineToPoint R
  let e := asIso (Q.map (toPoint C X))
  have hP : IsZero ((reducedDerivedChains.{d, u + 1} C J).obj P) :=
    DerivedCategory.Q.map_isZero (isZero_reducedCochains_obj_of_isZero J P (point_isZero C))
  let : Subsingleton ((reducedHypercohomology.{d, u + 1} C J (motivicSheafComplex k q) n).obj
      (op P)) := ⟨fun f g => hP.eq_of_src f g⟩
  exact ((E X).symm.trans
    ((Iso.homCongr e (Iso.refl _)).trans (E P))).injective.subsingleton

private theorem subsingleton_reducedMotivicHomFromPointedAffineLine_shift (n : ℤ) (q : ℕ) :
    Subsingleton (((reducedDerivedChains.{d, u + 1} C J).obj X)⟦(1 : ℤ)⟧ ⟶
      (DerivedCategory.Q.obj (motivicSheafComplex k q))⟦n⟧) := by
  let K := DerivedCategory.Q.obj (motivicSheafComplex k q)
  let A := Sheaf J AddCommGrpCat.{u + 1}
  let D := DerivedCategory A
  let F := shiftFunctor D (1 : ℤ)
  let e : (K⟦n - 1⟧)⟦(1 : ℤ)⟧ ≅ K⟦n⟧ :=
    (shiftFunctorAdd D (n - 1) 1).symm.app K ≪≫
      eqToIso (congrArg (fun p : ℤ => K⟦p⟧) (sub_add_cancel n 1))
  refine ⟨fun f g => ?_⟩
  apply (cancel_mono e.inv).1
  obtain ⟨f', hf⟩ := F.map_surjective (f ≫ e.inv)
  obtain ⟨g', hg⟩ := F.map_surjective (g ≫ e.inv)
  rw [← hf, ← hg,
    (subsingleton_reducedMotivicHomFromPointedAffineLine k (n - 1) q).elim f' g']

/-- The actual Tate cone collapse to the suspension gives a reduced motivic
cohomology isomorphism in every degree and weight. -/
@[colib_tag "COL-1038"]
theorem isIso_reducedMotivicHypercohomology_map_tateConeToSuspension
    (n : ℤ) (q : ℕ) :
    IsIso ((reducedHypercohomology.{d, u + 1} C J (motivicSheafComplex k q) n).map
      ((uliftPointed.{u + 1, u} C).map (tateConeToSuspension R)).op) := by
  obtain ⟨h, hs⟩ := exists_tateConeToSuspension_shortExact R
  let T := DerivedCategory.triangleOfSES hs
  let V := (DerivedCategory.Q.obj (motivicSheafComplex k q))⟦n⟧
  apply (ConcreteCategory.isIso_iff_bijective _).2
  change Function.Bijective (fun a : T.obj₃ ⟶ V => T.mor₂ ≫ a)
  exact bijective_precomp_mor₂_of_subsingleton T
    (DerivedCategory.triangleOfSES_distinguished hs) V
    (subsingleton_reducedMotivicHomFromPointedAffineLine k n q)
    (subsingleton_reducedMotivicHomFromPointedAffineLine_shift k n q)

/-- The original Tate connecting map gives the suspension comparison on
reduced motivic cohomology. -/
@[colib_tag "COL-1038",
  colib_ref "MorelVoevodsky1999" "Section 3.2, Lemma 2.15, p. 111" "ingredient"
    "The comparison of the pointed Tate quotient with the suspended torus"]
theorem bijective_precomp_tateSphereConnecting (n : ℤ) (q : ℕ) :
    Function.Bijective (fun a :
        ((reducedDerivedChains.{d, u + 1} C J).obj
          ((uliftPointed.{u + 1, u} C).obj (pointedTorus R)))⟦(1 : ℤ)⟧ ⟶
          (DerivedCategory.Q.obj (motivicSheafComplex k q))⟦n⟧ =>
      tateSphereConnecting R ≫ a) := by
  let T := DerivedCategory.triangleOfSES (tateSphereReducedCochainSequence_shortExact R)
  let V := (DerivedCategory.Q.obj (motivicSheafComplex k q))⟦n⟧
  let A := Sheaf J AddCommGrpCat.{u + 1}
  have hT : T ∈ distTriang (DerivedCategory A) :=
    DerivedCategory.triangleOfSES_distinguished (tateSphereReducedCochainSequence_shortExact R)
  change Function.Bijective (fun a : T.rotate.obj₃ ⟶ V => T.rotate.mor₂ ≫ a)
  exact bijective_precomp_mor₂_of_subsingleton T.rotate (rot_of_distTriang T hT) V
    (subsingleton_reducedMotivicHomFromPointedAffineLine k n q)
    (subsingleton_reducedMotivicHomFromPointedAffineLine_shift k n q)

end Motivic

end AlgebraicGeometry.MotivicHomotopy
