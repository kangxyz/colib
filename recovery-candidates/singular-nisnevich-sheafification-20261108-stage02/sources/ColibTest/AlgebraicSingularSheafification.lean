/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Simplex.NisnevichSheafification
import Mathlib.Data.ZMod.Basic

/-! # Exact ordinary chains and actual Nisnevich sheafification consumers -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite AlgebraicSimplex
open AlgebraicGeometry.Scheme

universe u v w a b

variable (R : Type u) [CommRing R]
variable {A : Type v} [Category.{w} A] [Abelian A]

example (K : Type a) [Category.{b} K] [HasLimitsOfShape K A] :
    PreservesLimitsOfShape K (singularChainsFunctor R (A := A)) := inferInstance

example (K : Type a) [Category.{b} K] [HasColimitsOfShape K A] :
    PreservesColimitsOfShape K (singularChainsFunctor R (A := A)) := inferInstance

example : (singularChainsFunctor R (A := A)).PreservesHomology :=
  singularChainsFunctor_preservesHomology R

example (S : ShortComplex ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)) (h : S.ShortExact) :
    (S.map (singularChainsFunctor R)).ShortExact :=
  singularChainsFunctor_map_shortExact R S h

-- The concrete large coefficient universe supplies actual sheafification.
example : HasSheafify (SmoothSite.nisnevichTopology (Spec (.of R)))
    AddCommGrpCat.{u + 1} := inferInstance

-- No reducedness, domain or field hypothesis is needed.
example : HasSheafify (SmoothSite.nisnevichTopology (Spec (.of (ZMod 6))))
    AddCommGrpCat.{1} := inferInstance

local notation "J" => SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of R))) A]
variable (P : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)

example (n : ℕ) : ((nisnevichSingularChainsFunctor R).obj P).X n =
    (presheafToSheaf J A).obj (((singularChainsFunctor R).obj P).X n) := rfl

example (i j : ℕ) : ((nisnevichSingularChainsFunctor R).obj P).d i j =
    (presheafToSheaf J A).map (((singularChainsFunctor R).obj P).d i j) := rfl

example {Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) :
    ((nisnevichSingularChainsFunctor R).map α).f n =
      (presheafToSheaf J A).map (((singularChainsFunctor R).map α).f n) := rfl

example (n : ℕ) : (singularChainsToNisnevichSheafification R P).f n =
    toSheafify J (((singularChainsFunctor R).obj P).X n) := rfl

example {Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A} (α : P ⟶ Q) :
    (singularChainsFunctor R).map α ≫ singularChainsToNisnevichSheafification R Q =
      singularChainsToNisnevichSheafification R P ≫
        ((sheafToPresheaf J A).mapHomologicalComplex (ComplexShape.down ℕ)).map
          ((nisnevichSingularChainsFunctor R).map α) :=
  singularChainsToNisnevichSheafification_naturality R α

example (n : ℕ) : Nonempty
    (((nisnevichSingularChainsFunctor R).obj P).homology n ≅
      (presheafToSheaf J A).obj (((singularChainsFunctor R).obj P).homology n)) :=
  ⟨nisnevichSingularHomologyIso R P n⟩

example {Q : (SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) :
    HomologicalComplex.homologyMap ((nisnevichSingularChainsFunctor R).map α) n ≫
      (nisnevichSingularHomologyIso R Q n).hom =
        (nisnevichSingularHomologyIso R P n).hom ≫
          (presheafToSheaf J A).map
            (HomologicalComplex.homologyMap ((singularChainsFunctor R).map α) n) :=
  nisnevichSingularHomologyIso_hom_naturality R α n

example (S : ShortComplex ((SmoothSite (Spec (.of R)))ᵒᵖ ⥤ A)) (h : S.ShortExact) :
    (S.map (nisnevichSingularChainsFunctor R)).ShortExact :=
  nisnevichSingularChainsFunctor_map_shortExact R S h

example (K : Type a) [Category.{b} K] [HasColimitsOfShape K A] :
    PreservesColimitsOfShape K (nisnevichSingularChainsFunctor R (A := A)) := inferInstance
