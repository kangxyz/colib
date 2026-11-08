module

import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.DistinguishedSquare
import Mathlib.Algebra.Category.Grp.Basic

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

example {X : Scheme.{u}} {R : Presieve X}
    (he : ∀ ⦃Y : Scheme.{u}⦄ (f : Y ⟶ X), R f → Etale f)
    (hl : ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ X),
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X), R f ∧
        ∃ y : Spec (.of K) ⟶ Y, y ≫ f = x) : R ∈ Nisnevich.precoverage X :=
  Nisnevich.mem_precoverage_of_field_lifting he hl

example {A X Y Z : Scheme.{u}}
    (i : A ⟶ X) [IsOpenImmersion i] (p : Y ⟶ X)
    (z : Z ⟶ X) [IsClosedImmersion z]
    (hcomp : Set.range z = (Set.range i)ᶜ) [IsIso (pullback.snd p z)]
    {K : Type u} [Field K] (x : Spec (.of K) ⟶ X) :
    (∃ a : Spec (.of K) ⟶ A, a ≫ i = x) ∨
      (∃ y : Spec (.of K) ⟶ Y, y ≫ p = x) :=
  Scheme.exists_field_lift_open_or_etale i p z hcomp x

section Generic

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (sq : Square C) [Mono sq.f₂₄]
  [HasPullback sq.f₁₂ sq.f₁₂] [HasPullback sq.f₃₄ sq.f₃₄]
  (hpb : sq.IsPullback)
  (hcover : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ ∈ J sq.X₄)
  (hdiag : Sieve.ofTwoArrows (pullback.diagonal sq.f₃₄) sq.overlapMap ∈
    J (pullback sq.f₃₄ sq.f₃₄))

example (F : Sheaf J AddCommGrpCat.{w}) :
    (sq.op.map F.obj).IsPullback :=
  sq.isPullback_op_map_of_diagonal_cover hpb hcover hdiag F

example : sq.overlapMap ≫ pullback.fst _ _ = pullback.fst _ _ ≫ sq.f₁₃ :=
  sq.overlapMap_fst

end Generic

section Smooth

open Scheme.SmoothSite

variable {S : Scheme.{u}} (sq : Square (Scheme.SmoothSite S)) (hpb : sq.IsPullback)
  [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
  {Z : Scheme.{u}} (z : Z ⟶ sq.X₄.left) [IsClosedImmersion z]
  (hcomp : Set.range z = (Set.range sq.f₂₄.left)ᶜ)
  [IsIso (pullback.snd sq.f₃₄.left z)]

example : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ ∈ nisnevichTopology S sq.X₄ :=
  ofTwoArrows_mem_nisnevichTopology_of_iso_complement sq.f₂₄ sq.f₃₄ z hcomp

example {A : Type v} [Category.{w} A] (F : Sheaf (nisnevichTopology S) A) :
    (sq.op.map F.obj).IsPullback :=
  isPullback_op_map_of_iso_complement sq hpb z hcomp F

example (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{v}) :
    (sq.op.map F.obj).IsPullback :=
  isPullback_op_map_of_iso_complement sq hpb z hcomp F

example [HasWeakSheafify (nisnevichTopology S) (Type u)] :
    (nisnevichTopology S).MayerVietorisSquare :=
  mayerVietorisSquareOfIsoComplement sq hpb z hcomp

example [HasWeakSheafify (nisnevichTopology S) (Type u)] :
    (mayerVietorisSquareOfIsoComplement sq hpb z hcomp).toSquare = sq :=
  mayerVietorisSquareOfIsoComplement_toSquare sq hpb z hcomp

example [HasWeakSheafify (nisnevichTopology S) (Type u)]
    (F : Sheaf (nisnevichTopology S) (Type u)) :
    (mayerVietorisSquareOfIsoComplement sq hpb z hcomp).SheafCondition F.obj :=
  (mayerVietorisSquareOfIsoComplement sq hpb z hcomp).sheafCondition_of_sheaf F

end Smooth
