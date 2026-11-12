module

import Colib.AlgebraicGeometry.Modules.Limits.BaseChangeBoundaryFrames

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits

universe u

set_option maxHeartbeats 800000 in
-- This regression expands the literal native base changes rather than assuming their limits.
example {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : I) (X Y : Over (D.obj i)) (b : X ⟶ Y)
    [CompactSpace X.left] [QuasiSeparatedSpace X.left]
    (a : Over i) (M : ((baseChangeDiagram D i Y).obj a).Modules) [M.IsFinitePresentation]
    (eLim : (Scheme.Modules.pullback (baseChangeMap (c.π.app i) X Y b)).obj
      ((Scheme.Modules.pullback ((baseChangeCone D c i Y).π.app a)).obj M) ≅
        SheafOfModules.unit (baseChangeCone D c i X).pt.ringCatSheaf) :
    ∃ (j : Over i) (f : j ⟶ a),
      Nonempty ((Scheme.Modules.pullback (baseChangeMap (D.map j.hom) X Y b)).obj
        ((Scheme.Modules.pullback ((baseChangeDiagram D i Y).map f)).obj M) ≅
          SheafOfModules.unit ((baseChangeDiagram D i X).obj j).ringCatSheaf) := by
  have : (SheafOfModules.unit
      ((baseChangeDiagram D i X).obj a).ringCatSheaf).IsFinitePresentation :=
    isFinitePresentation_unit _
  obtain ⟨j, f, e, _, _⟩ := exists_baseChange_boundary_frame_comp_eq_of_isLimit_finite
    D c hc i X Y b a M eLim
    (fun _ : Empty => SheafOfModules.unit ((baseChangeDiagram D i X).obj a).ringCatSheaf)
    (fun x => nomatch x) (fun x => nomatch x) (fun x => nomatch x)
  exact ⟨j, f, ⟨e⟩⟩
