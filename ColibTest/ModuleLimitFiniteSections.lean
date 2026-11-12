module

import Colib.AlgebraicGeometry.Modules.Limits.FiniteMorphisms

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits

universe u

-- The sections live only on the limit in the hypotheses. Both are actually constructed
-- at the common stage, and their original values are recovered through canonical maps.
example {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D) (hc : IsLimit c)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (i : I) (B : Fin 2 → (D.obj i).Modules) [∀ x, (B x).IsFinitePresentation]
    (s : ∀ x, ((Scheme.Modules.pullback (c.π.app i)).obj (B x)).sections) :
    ∃ (j : I) (e : j ⟶ i)
      (t : ∀ x, ((Scheme.Modules.pullback (D.map e)).obj (B x)).sections), ∀ x,
      (Scheme.Modules.pullbackUnitIso (c.π.app j)).inv ≫
          (Scheme.Modules.pullback (c.π.app j)).map ((SheafOfModules.unitHomEquiv _).symm (t x)) ≫
          canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) (B x) =
        (SheafOfModules.unitHomEquiv _).symm (s x) :=
  exists_sections_pullback_canonical_of_isLimit_finite D c hc i B s
