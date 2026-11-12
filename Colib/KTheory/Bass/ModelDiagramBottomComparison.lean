/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import Colib.CategoryTheory.Limits.Shapes.SequentialSystem.SignCorrection
public import Colib.KTheory.Bass.ModelDiagramTwoChartStableSequence
public import Colib.KTheory.Bass.StrictDiagramSuccessor
public import Colib.KTheory.Bass.TwoChart
public import Colib.Topology.Prespectrum.StableVanishing
public import Mathlib.Algebra.Category.Grp.Zero

/-!
Source: `Quillen/KTheory/Bass/ModelDiagramBottomComparison.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Bottom-degree Bass contraction of the actual coefficient Model stages

For any actual Model-valued coefficient functor, the original two Laurent chart maps on
the stage-i bottom signed group have cokernel the original stage-(i+1) bottom group.
The quotient map is the original Laurent cone inclusion and genuine signed loop shift.
No original seed-preservation, chart middle-exactness, or stabilization premise is used.
The original scheme/supported Bass recursions still need their geometric and K0 bridges.
-/

@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory CategoryTheory.Limits Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
universe u v w
namespace KTheory.Bass

/-- Actual signed groups of every original finite Model stage vanish below its offset. -/
theorem modelDiagramIterate_stable_subsingleton_of_lt
    {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    (i : ℕ) (F : C ⥤ WideSubcategory preservesZero.{w}) (X : C) (d : ℤ) (hd : d < -(i : ℤ)) :
    Subsingleton (stableHomotopyGroup
      (((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X) d) := by
  apply stableHomotopyGroup_subsingleton_of_stages _ d
  intro n
  let := modelDiagramIterate_homotopyGroup_subsingleton_of_le Q i F X
    ((-d).toNat + n + 2) (by omega) (d.toNat + n + 2) (by omega)
    ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).point
      ((-d).toNat + n + 2))
  exact inferInstanceAs (Subsingleton (Additive (HomotopyGroup.Pi (d.toNat + n + 2)
    ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).space
      ((-d).toNat + n + 2))
    ((((strictDiagramIterate Q i).obj (F ⋙ prespectrumFunctor)).obj X).point
      ((-d).toNat + n + 2)))))

variable {R : CommRingCat.{u}}
    (F : Under R ⥤ WideSubcategory preservesZero.{w}) (i : ℕ)

/-- The bottom signed groups with the original finite-stage coefficient maps. -/
def modelDiagramBottomFunctor : Under R ⥤ AddCommGrpCat.{w} :=
  modelDiagramTwoChartDiagram F i ⋙ stableHomotopyFunctor (-(i : ℤ))

/-- The original stage-i comparison cones with their unchanged coefficient actions. -/
def modelDiagramTwoChartConeDiagram : Under R ⥤ LoopPrespectrum.{w} :=
  laurentUnderSquareFunctor R ⋙ (modelDiagramTwoChartDiagram F i).mapArrow.mapArrow ⋙
    strictSquareComparisonFunctor ⋙ mappingConeFunctor

/-- The right endpoint of the original spectral row vanishes in the genuine lower range. -/
theorem modelDiagramTwoChartRight_isZero_of_lt (a : Under R) (d : ℤ)
    (hd : d < -(i : ℤ)) :
    IsZero (KTheory.Bass.TwoChartStable.bassRightGroup (modelDiagramTwoChartSquare F i a) d) := by
  let P := (stableHomotopyFunctor d).obj
    ((modelDiagramTwoChartDiagram F i).obj ((polynomialUnderFunctor R).obj a))
  let : Subsingleton P := modelDiagramIterate_stable_subsingleton_of_lt
    (laurentUnderSquareFunctor R) i F ((polynomialUnderFunctor R).obj a) d hd
  have hP : IsZero P := AddCommGrpCat.isZero_of_subsingleton P
  have hCharts : IsZero (P ⊞ P) := by
    rw [IsZero.iff_id_eq_zero]
    apply biprod.hom_ext <;> exact hP.eq_of_tgt _ _
  have hCoker : IsZero (cokernel (KTheory.Bass.TwoChartStable.strictOverlap
      (modelDiagramTwoChartSquare F i a) d)) :=
    IsZero.of_epi_eq_zero (cokernel.π (KTheory.Bass.TwoChartStable.strictOverlap
      (modelDiagramTwoChartSquare F i a) d)) (hCharts.eq_of_src _ _)
  let : Subsingleton (cokernel (KTheory.Bass.TwoChartStable.strictOverlap
      (modelDiagramTwoChartSquare F i a) d) : AddCommGrpCat.{w}) :=
    AddCommGrpCat.subsingleton_of_isZero hCoker
  let : Subsingleton (KTheory.Bass.TwoChartStable.bassRightGroup
      (modelDiagramTwoChartSquare F i a) d : AddCommGrpCat.{w}) := by
    change Subsingleton (AddMonoidHom.ker
      (KTheory.Bass.TwoChartStable.spanComparison (modelDiagramTwoChartSquare F i a) d).hom)
    infer_instance
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- It is the original left map, rather than a replacement abstract isomorphism, that is invertible.
-/
theorem modelDiagramTwoChartLeft_isIso_of_lt (a : Under R) (d : ℤ)
    (hd : d < -(i : ℤ)) : IsIso (modelDiagramTwoChartSequence F i a d).f :=
  (modelDiagramTwoChartSequence_shortExact F i a d).isIso_f_iff.mpr
    (modelDiagramTwoChartRight_isZero_of_lt F i a d hd)

/-- The chart-difference cokernel identified with the cone stable homotopy group in degree `e`, when
`d < -i` and `d + 1 = e`.
-/
def modelDiagramCokerConeIso (a : Under R) (d e : ℤ)
    (hd : d < -(i : ℤ)) (he : d + 1 = e) :
    cokernel (KTheory.Bass.TwoChartStable.chartDifference (modelDiagramTwoChartSquare F i a)
      e) ≅
    (stableHomotopyFunctor e).obj ((modelDiagramTwoChartConeDiagram F i).obj a) := by
  subst e
  let : IsIso (modelDiagramTwoChartSequence F i a d).f :=
    modelDiagramTwoChartLeft_isIso_of_lt F i a d hd
  exact asIso (modelDiagramTwoChartSequence F i a d).f ≪≫
    KTheory.Bass.TwoChartStable.bassShift (modelDiagramTwoChartSquare F i a) d

theorem modelDiagramCokerConeIso_π (a : Under R) (d e : ℤ)
    (hd : d < -(i : ℤ)) (he : d + 1 = e) :
    cokernel.π (KTheory.Bass.TwoChartStable.chartDifference (modelDiagramTwoChartSquare F i a)
      e) ≫ (modelDiagramCokerConeIso F i a d e hd he).hom =
    (stableHomotopyFunctor e).map
      (mappingConeInclusion (StrictSquare.comparison (modelDiagramTwoChartSquare F i a))) := by
  subst e
  exact KTheory.Bass.TwoChartStable.bassLeft_π_shift _
    (modelDiagramTwoChartSpectralConditions F i a) d

/-- The cokernel of the actual original chart difference is the actual cone group at the bottom.
-/
def modelDiagramBottomConeIso (a : Under R) :
    (KTheory.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (modelDiagramBottomFunctor F i)).obj a ≅
    (modelDiagramTwoChartConeDiagram F i ⋙ stableHomotopyFunctor (-(i : ℤ))).obj a := by
  exact modelDiagramCokerConeIso F i a (-(i : ℤ) - 1) (-(i : ℤ)) (by omega) (by omega)

/-- The bottom quotient retains the literal Laurent inclusion into the original stage-i cone. -/
@[reassoc]
theorem modelDiagramBottomConeIso_π (a : Under R) :
    (KTheory.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
      (modelDiagramBottomFunctor F i)).app a ≫ (modelDiagramBottomConeIso F i a).hom =
    (stableHomotopyFunctor (-(i : ℤ))).map
      (mappingConeInclusion (StrictSquare.comparison (modelDiagramTwoChartSquare F i a))) := by
  exact modelDiagramCokerConeIso_π F i a (-(i : ℤ) - 1) (-(i : ℤ)) (by omega) (by omega)

/-- Actual coefficient maps, including both chart actions, preserve the cone-cokernel comparison.
-/
@[reassoc]
theorem modelDiagramBottomConeIso_naturality {a b : Under R} (g : a ⟶ b) :
    (KTheory.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (modelDiagramBottomFunctor F i)).map g ≫ (modelDiagramBottomConeIso F i b).hom =
    (modelDiagramBottomConeIso F i a).hom ≫ (stableHomotopyFunctor (-(i : ℤ))).map
      ((modelDiagramTwoChartConeDiagram F i).map g) := by
  apply (cancel_epi ((KTheory.Bass.TwoChart.contractionπ (underToLaurent R)
    (underToLaurentInvert R) (modelDiagramBottomFunctor F i)).app a)).mp
  rw [← Category.assoc, ← (KTheory.Bass.TwoChart.contractionπ (underToLaurent R)
    (underToLaurentInvert R) (modelDiagramBottomFunctor F i)).naturality g, Category.assoc,
    modelDiagramBottomConeIso_π, ← Category.assoc, modelDiagramBottomConeIso_π]
  exact KTheory.Bass.TwoChartStable.comparisonConeMap_inclusion
    (modelDiagramTwoChartSquareMap F i g) (-(i : ℤ))

/-- The actual cone-cokernel comparison is natural on the full original coefficient category. -/
def modelDiagramBottomConeNatIso :
    KTheory.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (modelDiagramBottomFunctor F i) ≅
    modelDiagramTwoChartConeDiagram F i ⋙ stableHomotopyFunctor (-(i : ℤ)) :=
  NatIso.ofComponents (modelDiagramBottomConeIso F i)
    (fun g => modelDiagramBottomConeIso_naturality F i g)

/-- The real right-composition iteration identity identifies the next original finite stage. -/
theorem modelDiagramTwoChartDiagram_succ_loopedCone :
    modelDiagramTwoChartDiagram F (i + 1) =
      modelDiagramTwoChartConeDiagram F i ⋙ parameterLoopingFunctor :=
  congrArg (fun G : (Under R ⥤ LoopPrespectrum.{w}) ⥤ (Under R ⥤ LoopPrespectrum.{w}) =>
    G.obj (F ⋙ prespectrumFunctor))
      (strictDiagramIterate_succ_right (laurentUnderSquareFunctor R) i)

/-- The equality-induced successor comparison keeps every original coefficient map. -/
def modelDiagramTwoChartSuccessorIso :
    modelDiagramTwoChartDiagram F (i + 1) ≅
      modelDiagramTwoChartConeDiagram F i ⋙ parameterLoopingFunctor :=
  eqToIso (modelDiagramTwoChartDiagram_succ_loopedCone F i)

/-- The next-stage signed stable functor uses the genuine parameter-loop shift. -/
def modelDiagramStableSuccessorIso (d : ℤ) :
    modelDiagramTwoChartDiagram F (i + 1) ⋙ stableHomotopyFunctor d ≅
      modelDiagramTwoChartConeDiagram F i ⋙ stableHomotopyFunctor (d + 1) :=
  Functor.isoWhiskerRight (modelDiagramTwoChartSuccessorIso F i) (stableHomotopyFunctor d) ≪≫
    NatIso.ofComponents
      (fun a => parameterStableHomotopyIso ((modelDiagramTwoChartConeDiagram F i).obj a) d)
      (fun g => parameterStableHomotopyIso_naturality
        ((modelDiagramTwoChartConeDiagram F i).map g) d)

/-- Every stable-stage representative retains its genuine alternating sign and tail reindexing.
-/
theorem modelDiagramStableSuccessorIso_ι_hom (d : ℤ) (a : Under R) (n : ℕ) :
    stableHomotopyι ((modelDiagramTwoChartDiagram F (i + 1)).obj a) d n ≫
      (modelDiagramStableSuccessorIso F i d).hom.app a =
    (stableSystemMap ((modelDiagramTwoChartSuccessorIso F i).hom.app a) d).app n ≫
      (SequentialSystem.alternatingIso n
        (parameterStableStageIso ((modelDiagramTwoChartConeDiagram F i).obj a) d n)).hom ≫
      (shiftedStableReindexIso ((modelDiagramTwoChartConeDiagram F i).obj a) d n).hom ≫
      stableHomotopyι ((modelDiagramTwoChartConeDiagram F i).obj a) (d + 1)
        (parameterStableOffset d + n) := by
  change stableHomotopyι _ d n ≫
    ((stableHomotopyFunctor d).map ((modelDiagramTwoChartSuccessorIso F i).hom.app a) ≫
      (parameterStableHomotopyIso ((modelDiagramTwoChartConeDiagram F i).obj a) d).hom) = _
  rw [← Category.assoc, stableHomotopyι_naturality, Category.assoc]
  exact congrArg
    (fun k => (stableSystemMap ((modelDiagramTwoChartSuccessorIso F i).hom.app a) d).app n ≫ k)
    (parameterStableHomotopyIso_ι_hom ((modelDiagramTwoChartConeDiagram F i).obj a) d n)

/-- The bottom successor is the genuine signed parameter-loop shift, with its integer transport.
-/
def modelDiagramBottomSuccessorIso :
    modelDiagramBottomFunctor F (i + 1) ≅
      modelDiagramTwoChartConeDiagram F i ⋙ stableHomotopyFunctor (-(i : ℤ)) :=
  modelDiagramStableSuccessorIso F i (-((i + 1 : ℕ) : ℤ)) ≪≫
    Functor.isoWhiskerLeft (modelDiagramTwoChartConeDiagram F i)
      (eqToIso (congrArg (fun d : ℤ => stableHomotopyFunctor.{w} d)
        (show -((i + 1 : ℕ) : ℤ) + 1 = -(i : ℤ) by omega)))

/-- The component keeps the signed loop shift and the exact integer-degree transport explicit.
-/
theorem modelDiagramBottomSuccessorIso_hom_app (a : Under R) :
    (modelDiagramBottomSuccessorIso F i).hom.app a =
    (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((modelDiagramTwoChartSuccessorIso F i).hom.app a) ≫
      (parameterStableHomotopyIso ((modelDiagramTwoChartConeDiagram F i).obj a)
        (-((i + 1 : ℕ) : ℤ))).hom ≫
      eqToHom (congrArg
        (fun d : ℤ => stableHomotopyGroup ((modelDiagramTwoChartConeDiagram F i).obj a) d)
        (show -((i + 1 : ℕ) : ℤ) + 1 = -(i : ℤ) by omega)) := by
  simp only [modelDiagramBottomSuccessorIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, eqToIso.hom, eqToHom_app]
  rfl

/-- The inverse comparison uses the genuine inverse parameter-stable shift, with no extra sign.
-/
theorem modelDiagramBottomSuccessorIso_inv_app (a : Under R) :
    (modelDiagramBottomSuccessorIso F i).inv.app a =
    eqToHom (congrArg
        (fun d : ℤ => stableHomotopyGroup ((modelDiagramTwoChartConeDiagram F i).obj a) d)
        (show -(i : ℤ) = -((i + 1 : ℕ) : ℤ) + 1 by omega)) ≫
      (parameterStableHomotopyIso ((modelDiagramTwoChartConeDiagram F i).obj a)
        (-((i + 1 : ℕ) : ℤ))).inv ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((modelDiagramTwoChartSuccessorIso F i).inv.app a) := by
  simp only [modelDiagramBottomSuccessorIso, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, eqToIso.inv, eqToHom_app]
  rfl

/-- The genuine contraction of the actual bottom functor is the next original finite bottom. -/
def modelDiagramBottomContractionIso :
    KTheory.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
      (modelDiagramBottomFunctor F i) ≅ modelDiagramBottomFunctor F (i + 1) :=
  modelDiagramBottomConeNatIso F i ≪≫ (modelDiagramBottomSuccessorIso F i).symm

/-- Every Laurent representative is the original cone inclusion followed by inverse signed shift.
The successor comparison contains the genuine loop shift and actual equality-induced transports.
-/
@[reassoc]
theorem modelDiagramBottomContractionIso_π (a : Under R) :
    (KTheory.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
      (modelDiagramBottomFunctor F i)).app a ≫
        (modelDiagramBottomContractionIso F i).hom.app a =
    (stableHomotopyFunctor (-(i : ℤ))).map
      (mappingConeInclusion (StrictSquare.comparison (modelDiagramTwoChartSquare F i a))) ≫
        (modelDiagramBottomSuccessorIso F i).inv.app a := by
  simp only [modelDiagramBottomContractionIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    ← Category.assoc]
  rw [show (modelDiagramBottomConeNatIso F i).hom.app a =
      (modelDiagramBottomConeIso F i a).hom from rfl, modelDiagramBottomConeIso_π]

/-- Applying the actual forward signed successor shift recovers precisely the original inclusion.
-/
@[reassoc]
theorem modelDiagramBottomContractionIso_π_shift (a : Under R) :
    (KTheory.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
      (modelDiagramBottomFunctor F i)).app a ≫
      (modelDiagramBottomContractionIso F i).hom.app a ≫
      (modelDiagramBottomSuccessorIso F i).hom.app a =
    (stableHomotopyFunctor (-(i : ℤ))).map
      (mappingConeInclusion (StrictSquare.comparison (modelDiagramTwoChartSquare F i a))) := by
  rw [← Category.assoc, modelDiagramBottomContractionIso_π, Category.assoc,
    Iso.inv_hom_id_app]
  change (stableHomotopyFunctor (-(i : ℤ))).map
    (mappingConeInclusion (StrictSquare.comparison (modelDiagramTwoChartSquare F i a))) ≫
    𝟙 ((stableHomotopyFunctor (-(i : ℤ))).obj
      (mappingCone (StrictSquare.comparison (modelDiagramTwoChartSquare F i a)))) = _
  exact Category.comp_id _

end KTheory.Bass
