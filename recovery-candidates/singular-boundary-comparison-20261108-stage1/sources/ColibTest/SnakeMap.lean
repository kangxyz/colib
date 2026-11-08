module

import Colib.Algebra.Homology.SnakeMap

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u₂ v₂
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable (S : ShortComplex.SnakeInput C)

example : (S.map F).L₀ = S.L₀.map F := rfl
example : (S.map F).L₃ = S.L₃.map F := rfl
example : (S.map F).v₁₂ = F.mapShortComplex.map S.v₁₂ := rfl
example : (S.map F).δ = F.map S.δ := S.map_δ F
example : (S.map F).L₁.Exact := (S.map F).L₁_exact
example : (S.map F).L₂.Exact := (S.map F).L₂_exact
