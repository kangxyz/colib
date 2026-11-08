module

import Colib.Algebra.Homology.HomologySequenceMap

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u₁ v₁ u₂ v₂ u₃
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

example (S : ShortComplex C) :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := S.homologyπ_mapHomologyIso_hom F

example (S : ShortComplex C) :
    (S.mapHomologyIso F).hom ≫ F.map S.homologyι =
      (S.map F).homologyι ≫ (S.mapOpcyclesIso F).hom := S.mapHomologyIso_hom_homologyι F

example (S : ShortComplex (ChainComplex C ℕ)) (hS : S.ShortExact) (n : ℕ) :
    (hS.map_of_exact (F.mapHomologicalComplex (.down ℕ))).δ (n + 1) n rfl ≫
        ((S.X₁.sc n).mapHomologyIso F).hom =
      ((S.X₃.sc (n + 1)).mapHomologyIso F).hom ≫ F.map (hS.δ (n + 1) n rfl) :=
  HomologySequence.mapHomologyIso_hom_δ F hS (n + 1) n rfl

example (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact) (n : ℤ) :
    (hS.map_of_exact (F.mapHomologicalComplex (.up ℤ))).δ n (n + 1) rfl ≫
        ((S.X₁.sc (n + 1)).mapHomologyIso F).hom =
      ((S.X₃.sc n).mapHomologyIso F).hom ≫ F.map (hS.δ n (n + 1) rfl) :=
  HomologySequence.mapHomologyIso_hom_δ F hS n (n + 1) rfl
