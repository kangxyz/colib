module

import Colib.AlgebraicGeometry.Modules.Limits.FiniteIsomorphisms

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D) (hc : IsLimit c)
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

-- Two prescribed sections are retained by the same descended isomorphism, together with
-- the actual canonical equation identifying it with the specified limit isomorphism.
example (i : I) (A B : (D.obj i).Modules)
    [A.IsFinitePresentation] [B.IsFinitePresentation]
    (N : (Scheme.Modules.pullback (c.π.app i)).obj A ≅
      (Scheme.Modules.pullback (c.π.app i)).obj B)
    (a : Fin 2 → (SheafOfModules.unit (D.obj i).ringCatSheaf ⟶ A))
    (b : Fin 2 → (SheafOfModules.unit (D.obj i).ringCatSheaf ⟶ B))
    (h : ∀ x, (Scheme.Modules.pullback (c.π.app i)).map (a x) ≫ N.hom =
      (Scheme.Modules.pullback (c.π.app i)).map (b x)) :
    ∃ (j : I) (e : j ⟶ i)
      (m : (Scheme.Modules.pullback (D.map e)).obj A ≅
        (Scheme.Modules.pullback (D.map e)).obj B),
      ((Scheme.Modules.pullback (c.π.app j)).map m.hom ≫
          canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) B =
        canHom (c.π.app j) (D.map e) (c.π.app i) (c.w e) A ≫ N.hom) ∧
      ∀ x, (Scheme.Modules.pullback (D.map e)).map (a x) ≫ m.hom =
        (Scheme.Modules.pullback (D.map e)).map (b x) := by
  have : (SheafOfModules.unit (D.obj i).ringCatSheaf).IsFinitePresentation :=
    isFinitePresentation_unit _
  exact exists_iso_pullback_canonical_comp_eq_of_isLimit_finite D c hc i A B N
    (fun _ : Fin 2 => SheafOfModules.unit (D.obj i).ringCatSheaf) a b h
