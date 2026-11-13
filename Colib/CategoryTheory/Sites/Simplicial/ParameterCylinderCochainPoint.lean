/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.ParameterCoproductPoint
import Colib.Algebra.Homology.Embedding.MapExtend
import Colib.AlgebraicTopology.DoldKan.NormalizedMooreMap

/-!
# The parameter-point section on reduced cochains

The original point section is the inclusion of the actual point
summand on reduced presheaf cochains. The normalized Moore comparison
and the extension by zero both retain that inclusion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

open ParameterCoproduct

variable {C : Type u} [Category.{v} C] (V : C) [HasBinaryProducts C]
  (p : 𝟭 C ⟶ (Functor.const C).obj V)

omit [HasBinaryProducts C] in
private theorem normalizedParameterCoproduct_point
    (R : SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{max v w})) :
    let A := Cᵒᵖ ⥤ AddCommGrpCat.{max v w}
    let Φ := ParameterCoproduct.functor V AddCommGrpCat.{max v w}
    (homologicalPointInclusion V p _ (.down ℕ)).app ((normalizedMooreComplex A).obj R) ≫
        (normalizedMooreComplexCompMapHomologicalComplexIso Φ).hom.app R =
      (normalizedMooreComplex A).map ((simplicialPointInclusion V p _).app R) := by
  intro A Φ
  let c := ComplexShape.down ℕ
  let N := normalizedMooreComplex A
  let L := alternatingFaceMapComplex A
  let i := inclusionOfMooreComplex A
  let G := simplicialFunctor V AddCommGrpCat.{max v w}
  let φ := pointInclusion V p AddCommGrpCat.{max v w}
  let f := (simplicialPointInclusion V p AddCommGrpCat.{max v w}).app R
  let e := (normalizedMooreComplexCompMapHomologicalComplexIso Φ).app R
  let a := (alternatingFaceMapComplexCompMapHomologicalComplexIso Φ).hom.app R
  let j := (Φ.mapHomologicalComplex c).map (i.app R)
  let t := (homologicalPointInclusion V p _ c).app (N.obj R)
  have he : e.hom ≫ i.app (G.obj R) = j ≫ a :=
    NatTrans.congr_app
      (normalizedMooreComplexCompMapHomologicalComplexIso_hom_comp_inclusionOfMooreComplex Φ) R
  have hi : N.map f ≫ i.app (G.obj R) = i.app R ≫ L.map f := i.naturality f
  let : Mono (i.app (G.obj R)) :=
    inferInstanceAs (Mono (inclusionOfMooreComplexMap (G.obj R)))
  apply (cancel_mono (i.app (G.obj R))).1
  calc
    _ = t ≫ (e.hom ≫ i.app (G.obj R)) := Category.assoc _ _ _
    _ = t ≫ j ≫ a := congrArg (t ≫ ·) he
    _ = i.app R ≫ L.map f := by
      apply HomologicalComplex.hom_ext
      intro n
      have h : φ.app ((N.obj R).X n) ≫ Φ.map ((i.app R).f n) =
          (i.app R).f n ≫ φ.app (R.obj (op ⦋n⦌)) := (φ.naturality ((i.app R).f n)).symm
      change (𝟙 _ ≫ φ.app ((N.obj R).X n)) ≫ (Φ.map ((i.app R).f n) ≫ 𝟙 _) =
        (i.app R).f n ≫ φ.app (R.obj (op ⦋n⦌))
      exact (congrArg (fun m => m ≫ (Φ.map ((i.app R).f n) ≫ 𝟙 _))
        (Category.id_comp _)).trans
        ((congrArg (φ.app ((N.obj R).X n) ≫ ·) (Category.comp_id _)).trans h)
    _ = _ := hi.symm

omit [HasBinaryProducts C] in
private theorem reducedChainsParameterCylinderIso_hom_point
    (X : PointedSimplicialPresheaf.{max v w} C) :
    (reducedChains C).map (cylinderSection X
        (show (⊤_ (Cᵒᵖ ⥤ SSet.{max v w})) ⟶ liftedRepresentableInterval.{w} V from
          liftedParameterPoint (C := C) V p)) ≫
        (reducedChainsParameterCylinderIso.{w} V X).hom =
      (homologicalPointInclusion V p _ (.down ℕ)).app ((reducedChains C).obj X) := by
  let A := Cᵒᵖ ⥤ AddCommGrpCat.{max v w}
  let Φ := ParameterCoproduct.functor V AddCommGrpCat.{max v w}
  let R := (reducedFreeAbelian C).obj X
  let N := normalizedMooreComplex A
  let i := cylinderSection X
    (show (⊤_ (Cᵒᵖ ⥤ SSet.{max v w})) ⟶ liftedRepresentableInterval.{w} V from
      liftedParameterPoint (C := C) V p)
  let f := (reducedFreeAbelian C).map i
  let s := reducedFreeAbelianParameterCylinderIso.{w} V X
  let e := (normalizedMooreComplexCompMapHomologicalComplexIso Φ).app R
  let a := (homologicalPointInclusion V p _ (.down ℕ)).app (N.obj R)
  let b := (simplicialPointInclusion V p _).app R
  have hs : f ≫ s.hom = b := reducedFreeAbelianParameterCylinderIso_hom_point V p X
  have ha : a ≫ e.hom = N.map b := normalizedParameterCoproduct_point V p R
  rw [reducedChainsParameterCylinderIso_hom_eq]
  change N.map f ≫ N.map s.hom ≫ e.inv = a
  calc
    _ = N.map (f ≫ s.hom) ≫ e.inv := (N.map_comp_assoc _ _ _).symm
    _ = N.map b ≫ e.inv := congrArg (fun t => N.map t ≫ e.inv) hs
    _ = (a ≫ e.hom) ≫ e.inv := congrArg (· ≫ e.inv) ha.symm
    _ = _ := (Category.assoc _ _ _).trans
      ((congrArg (a ≫ ·) e.hom_inv_id).trans (Category.comp_id _))

omit [HasBinaryProducts C] in
private theorem mapExtendIso_hom_point {ι ι' : Type*} {c : ComplexShape ι}
    {c' : ComplexShape ι'} (e : c.Embedding c')
    (K : HomologicalComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max v w}) c) :
    let Φ := ParameterCoproduct.functor V AddCommGrpCat.{max v w}
    (homologicalPointInclusion V p _ c').app (K.extend e) ≫ (K.mapExtendIso Φ e).hom =
      (e.extendFunctor _).map ((homologicalPointInclusion V p _ c).app K) := by
  intro Φ
  let i := (homologicalPointInclusion V p _ c).app K
  let a := pointInclusion V p AddCommGrpCat.{max v w}
  apply HomologicalComplex.hom_ext
  intro n
  change (𝟙 _ ≫ a.app (HomologicalComplex.extend.X K (e.r n))) ≫
      (HomologicalComplex.extend.mapXIso K Φ (e.r n)).hom =
    HomologicalComplex.extend.mapX i (e.r n)
  generalize e.r n = m
  cases m with
  | none => exact (HomologicalComplex.extend.isZero_X K rfl).eq_of_src _ _
  | some m =>
    change (𝟙 _ ≫ a.app (K.X m)) ≫ 𝟙 _ = 𝟙 _ ≫ a.app (K.X m)
    exact Category.comp_id _

omit [HasBinaryProducts C] in
/-- The reduced cochain comparison takes the original cylinder section
to inclusion of the original point summand. -/
theorem reducedPresheafCochainsParameterCylinderIso_hom_point
    (X : PointedSimplicialPresheaf.{max v w} C) :
    (reducedPresheafCochains C).map (cylinderSection X
        (show (⊤_ (Cᵒᵖ ⥤ SSet.{max v w})) ⟶ liftedRepresentableInterval.{w} V from
          liftedParameterPoint (C := C) V p)) ≫
        (reducedPresheafCochainsParameterCylinderIso.{w} V X).hom =
      (homologicalPointInclusion V p _ (.up ℤ)).app ((reducedPresheafCochains C).obj X) := by
  let e := ComplexShape.embeddingUpIntLE 0
  let F := e.extendFunctor (Cᵒᵖ ⥤ AddCommGrpCat.{max v w})
  let Φ := ParameterCoproduct.functor V AddCommGrpCat.{max v w}
  let K := (reducedChains C).obj X
  let a := (reducedChains C).map (cylinderSection X
    (show (⊤_ (Cᵒᵖ ⥤ SSet.{max v w})) ⟶ liftedRepresentableInterval.{w} V from
      liftedParameterPoint (C := C) V p))
  let b := (reducedChainsParameterCylinderIso.{w} V X).hom
  let d := K.mapExtendIso Φ e
  let s := (homologicalPointInclusion V p _ (.down ℕ)).app K
  let t := (homologicalPointInclusion V p _ (.up ℤ)).app (K.extend e)
  have hs : a ≫ b = s := reducedChainsParameterCylinderIso_hom_point V p X
  have ht : t ≫ d.hom = F.map s := mapExtendIso_hom_point V p e K
  rw [reducedPresheafCochainsParameterCylinderIso_hom_eq]
  change F.map a ≫ F.map b ≫ d.inv = t
  calc
    _ = F.map (a ≫ b) ≫ d.inv := (F.map_comp_assoc _ _ _).symm
    _ = F.map s ≫ d.inv := congrArg (fun u => F.map u ≫ d.inv) hs
    _ = (t ≫ d.hom) ≫ d.inv := congrArg (· ≫ d.inv) ht.symm
    _ = _ := (Category.assoc _ _ _).trans
      ((congrArg (t ≫ ·) d.hom_inv_id).trans (Category.comp_id _))

end CategoryTheory.PointedSimplicialPresheaf
