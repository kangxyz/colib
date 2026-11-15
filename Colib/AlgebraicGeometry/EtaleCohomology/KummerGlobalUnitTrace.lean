/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleKummerDirectImage
public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleMultiplicativeTraceUnits
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerUnitsModulo
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleExtForgetPullback

/-! # Actual degree-zero direct-image and global-unit trace

The actual abelian constant source and direct image recover the sectionwise unit trace.
Module corestriction compatibility is a separate comparison.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
universe u
namespace Stacks.EtaleCohomology
open Stacks.Kummer
variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- The actual source morphism used to push a constant-source abelian Ext class. -/
def kummerH0PushSource :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      (etaleAbelianDirectImage.{u, 0} g).obj
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  (etaleAbelianInverseImageDirectImageAdj.{u, 0} g).unit.app _ ≫
    (etaleAbelianDirectImage.{u, 0} g).map
      ((etaleAbelianInverseImageConstantIso.{u, 0} g).hom.app _)

set_option backward.isDefEq.respectTransparency false in
/-- The source arrow is exactly the constant-adjunction comparison, on morphisms. -/
theorem kummerH0PushSource_transpose
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ F) :
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
        (etaleSiteTerminalIsTerminal X)).homEquiv _ _
      (kummerH0PushSource g ≫ (etaleAbelianDirectImage.{u, 0} g).map f) =
    (constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
        ((etaleSiteTerminalIsTerminal X).isTerminalObj
          (smallEtaleBaseChange g))).homEquiv _ _ f := by
  let a := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    (etaleSiteTerminalIsTerminal X)
  let b := etaleAbelianInverseImageDirectImageAdj.{u, 0} g
  let c := constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
    ((etaleSiteTerminalIsTerminal X).isTerminalObj (smallEtaleBaseChange g))
  have h : (a.comp b).homEquiv _ _
      ((etaleAbelianInverseImageConstantIso.{u, 0} g).hom.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))) = c.unit.app _ :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _
  have hh : (a.comp b).homEquiv _ _
      ((etaleAbelianInverseImageConstantIso.{u, 0} g).hom.app _ ≫ f) =
      c.homEquiv _ _ f := by
    rw [Adjunction.homEquiv_naturality_right, h, Adjunction.homEquiv_unit]
    rfl
  have hb : b.homEquiv _ _
      ((etaleAbelianInverseImageConstantIso.{u, 0} g).hom.app _ ≫ f) =
      kummerH0PushSource g ≫ (etaleAbelianDirectImage.{u, 0} g).map f := by
    rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp]
    exact (Category.assoc _ _ _).symm
  rw [Adjunction.comp_homEquiv] at hh
  change a.homEquiv _ _ (b.homEquiv _ _
      ((etaleAbelianInverseImageConstantIso.{u, 0} g).hom.app _ ≫ f)) =
    c.homEquiv _ _ f at hh
  erw [hb] at hh
  exact hh

variable [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [Etale g] [IsFinite g]

/-- Push an actual abelian constant-source class through the exact direct image. -/
def kummerH0Push (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (x : Sheaf.H.{u + 1} F 0) :
    Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, 0} g).obj F) 0 :=
  (Ext.mk₀ (kummerH0PushSource g)).comp
    (x.mapExactFunctor (etaleAbelianDirectImage.{u, 0} g)) (zero_add 0)

omit [Etale g] in
set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the actual direct-image class uses the pulled-back terminal object. -/
theorem kummerH0Push_equiv₀
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (x : Sheaf.H.{u + 1} F 0) :
    Sheaf.H.equiv₀ _ (etaleSiteTerminalIsTerminal X) (kummerH0Push g F x) =
      Sheaf.H.equiv₀ F ((etaleSiteTerminalIsTerminal X).isTerminalObj
        (smallEtaleBaseChange g)) x := by
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ F).surjective x
  simp only [kummerH0Push, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply,
    ← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]
  change AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
        (etaleSiteTerminalIsTerminal X)).homEquiv _ _
          (kummerH0PushSource g ≫ (etaleAbelianDirectImage.{u, 0} g).map f)) =
    AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
        ((etaleSiteTerminalIsTerminal X).isTerminalObj
          (smallEtaleBaseChange g))).homEquiv _ _ f)
  rw [kummerH0PushSource_transpose]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Change the terminal evaluation without identifying the two terminal objects. -/
theorem kummerH0_equiv₀_changeTerminal
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    {T T' : Y.Etale} (hT : IsTerminal T) (hT' : IsTerminal T')
    (x : Sheaf.H.{u + 1} F 0) :
    F.obj.map (hT.from T').op (Sheaf.H.equiv₀ F hT x) =
      Sheaf.H.equiv₀ F hT' x := by
  let q := (sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
    _ F (Ext.addEquiv₀ x)
  change F.obj.map (hT.from T').op
      (q.app (op T) (ULift.up (1 : ℤ))) = q.app (op T') (ULift.up (1 : ℤ))
  simpa using congrArg (fun k => k (ULift.up (1 : ℤ)))
    (q.naturality (hT.from T').op).symm

set_option backward.isDefEq.respectTransparency false in
/-- The cohomological trace of a global unit is exactly the existing sectionwise trace. -/
theorem kummerH0_trace_globalUnit (t : Γ(Y, ⊤)ˣ) :
    Sheaf.H.map (finiteEtaleMultiplicativeTrace g) 0
        (kummerH0Push g (multiplicativeSheaf.{u, 0} Y)
          (globalUnitsH0Equiv Y (Additive.ofMul t))) =
      globalUnitsH0Equiv X (Additive.ofMul
        (finiteEtaleMultiplicativeTraceUnits g (Scheme.Etale.mk (𝟙 X)) t)) := by
  apply (Sheaf.H.equiv₀ _ (etaleSiteTerminalIsTerminal X)).injective
  rw [← Sheaf.H.equiv₀_naturality, kummerH0Push_equiv₀,
    ← kummerH0_equiv₀_changeTerminal (multiplicativeSheaf.{u, 0} Y)
      (etaleSiteTerminalIsTerminal Y)]
  simp only [globalUnitsH0Equiv, AddEquiv.coe_mk, Equiv.coe_fn_mk]
  let : MorphismProperty.ContainsIdentities (@Etale.{u}) := ⟨fun _ => inferInstance⟩
  have hterm (Z : Scheme.{u}) : etaleSiteTerminalIsTerminal Z =
      MorphismProperty.Over.mkIdTerminal (@Etale.{u}) Z := Subsingleton.elim _ _
  erw [hterm X, hterm Y]
  erw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  rfl

end Stacks.EtaleCohomology
end
