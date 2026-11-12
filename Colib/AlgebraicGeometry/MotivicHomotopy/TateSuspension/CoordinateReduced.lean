/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSphere
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.Coordinate
public import Colib.CategoryTheory.Sites.Simplicial.ReducedHypercohomology
public import Colib.CategoryTheory.Sites.Simplicial.UniverseLift
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# The relative source of the pointed torus

The terminal object of the smooth site represents the basepoint of the torus.
Degreewise free abelianization and sheafification therefore identify the
reduced object with the constant simplicial sheaf on the native relative
source. Under this comparison the reduction morphism is the quotient by the
actual free-Yoneda map of the identity section.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PointedSimplicialPresheaf Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.PresheafWithTransfers
open Stacks.Cohomology.FreeYonedaUnivLE

universe d u

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]

local notation "Rₖ" => CommRingCat.of k
local notation "Sₖ" => Spec Rₖ
local notation "Cₖ" => SmoothSite Sₖ
local notation "Jₖ" => SmoothSite.nisnevichTopology Sₖ

/-- The native torus pointed at one in the universe of the motivic coefficients. -/
abbrev liftedPointedTorus : PointedSimplicialPresheaf.{u + 1} Cₖ :=
  (uliftPointed.{u + 1, u} Cₖ).obj (pointedTorus Rₖ)

private abbrev liftedYoneda :
    Cₖ ⥤ Cₖᵒᵖ ⥤ SSet.{u + 1} :=
  CategoryTheory.uliftYoneda.{u + 1} ⋙ discretePresheaf Cₖ

private def baseIsTerminal : IsTerminal (base Sₖ) :=
  IsTerminal.ofUniqueHom Contraction.toBase fun X f => by
    apply MorphismProperty.Over.Hom.ext
    have h := MorphismProperty.Over.w f
    change f.left ≫ 𝟙 Sₖ = X.hom at h
    exact (Category.comp_id _).symm.trans h

private def liftedYonedaBaseIsoTerminal :
    (liftedYoneda k).obj (base Sₖ) ≅ ⊤_ (Cₖᵒᵖ ⥤ SSet.{u + 1}) := by
  let Y := liftedYoneda k
  let : PreservesLimit (Functor.empty.{0} Cₖ) Y := by
    dsimp [Y, liftedYoneda, CategoryTheory.uliftYoneda, discretePresheaf]
    infer_instance
  exact ((baseIsTerminal k).isTerminalObj Y).uniqueUpToIso terminalIsTerminal

private theorem liftedYonedaBaseIsoTerminal_hom_point :
    (liftedYonedaBaseIsoTerminal k).hom ≫ (liftedPointedTorus k).hom =
      (liftedYoneda k).map (torusOne Sₖ) := by
  apply NatTrans.ext
  funext U
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  change ULift.up (Contraction.toBase U.unop ≫ torusOne Sₖ) =
    ULift.up (x.down ≫ torusOne Sₖ)
  exact congrArg (fun f => ULift.up (f ≫ torusOne Sₖ))
    ((baseIsTerminal k).hom_ext _ _)

private abbrev simplicialSheafification :
    SimplicialObject (Cₖᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
      SimplicialObject (Sheaf Jₖ AddCommGrpCat.{u + 1}) :=
  (Functor.whiskeringRight _ _ _).obj (presheafToSheaf Jₖ AddCommGrpCat.{u + 1})

private abbrev freeAbelianSheaf :
    (Cₖᵒᵖ ⥤ SSet.{u + 1}) ⥤ SimplicialObject (Sheaf Jₖ AddCommGrpCat.{u + 1}) :=
  freeAbelian.{u + 1} Cₖ ⋙ simplicialSheafification k

private def freeAbelianSheafLiftedYonedaIso :
    liftedYoneda k ⋙ freeAbelianSheaf k ≅
      freeYoneda.{u + 1} Jₖ ⋙ SimplicialObject.const (Sheaf Jₖ AddCommGrpCat.{u + 1}) :=
  let F := (Functor.whiskeringRight Cₖᵒᵖ _ _).obj AddCommGrpCat.free
  Functor.isoWhiskerLeft CategoryTheory.uliftYoneda.{u + 1}
    (Functor.isoWhiskerRight (Functor.compConstIso (J := SimplexCategoryᵒᵖ) F).symm
      (simplicialSheafification k) ≪≫
      Functor.isoWhiskerLeft F
        (Functor.compConstIso (J := SimplexCategoryᵒᵖ)
          (presheafToSheaf Jₖ AddCommGrpCat.{u + 1})).symm)

private def torusBasepointCokernelIso :
    cokernel ((freeAbelianSheaf k).map (liftedPointedTorus k).hom) ≅
      cokernel ((SimplicialObject.const (Sheaf Jₖ AddCommGrpCat.{u + 1})).map
        ((freeYoneda.{u + 1} Jₖ).map (torusOne Sₖ))) := by
  let F := freeAbelianSheaf k
  let e := liftedYonedaBaseIsoTerminal k
  let D := freeAbelianSheafLiftedYonedaIso k
  let f := torusOne Sₖ
  have hs : e.hom ≫ (liftedPointedTorus k).hom = (liftedYoneda k).map f :=
    liftedYonedaBaseIsoTerminal_hom_point k
  have h : e.inv ≫ (liftedYoneda k).map f = (liftedPointedTorus k).hom :=
    (congrArg (fun t => e.inv ≫ t) hs).symm.trans (e.inv_hom_id_assoc _)
  let g := (SimplicialObject.const (Sheaf Jₖ AddCommGrpCat.{u + 1})).map
    ((freeYoneda.{u + 1} Jₖ).map f)
  have hn : F.map ((liftedYoneda k).map f) ≫ D.hom.app (multiplicativeGroupObject Sₖ) =
      D.hom.app (base Sₖ) ≫ g :=
    D.hom.naturality f
  refine cokernel.mapIso _ _
    (F.mapIso e.symm ≪≫ D.app (base Sₖ)) (D.app (multiplicativeGroupObject Sₖ)) ?_
  change F.map (liftedPointedTorus k).hom ≫ D.hom.app (multiplicativeGroupObject Sₖ) =
    (F.map e.inv ≫ D.hom.app (base Sₖ)) ≫ g
  calc
    _ = F.map (e.inv ≫ (liftedYoneda k).map f) ≫ D.hom.app (multiplicativeGroupObject Sₖ) :=
      congrArg (fun t => F.map t ≫ D.hom.app (multiplicativeGroupObject Sₖ)) h.symm
    _ = F.map e.inv ≫ F.map ((liftedYoneda k).map f) ≫
        D.hom.app (multiplicativeGroupObject Sₖ) := F.map_comp_assoc _ _ _
    _ = F.map e.inv ≫ D.hom.app (base Sₖ) ≫ g :=
      congrArg (fun t => F.map e.inv ≫ t) hn
    _ = _ := (Category.assoc _ _ _).symm

/-- The actual sheafified reduced free simplicial object on the pointed torus. -/
@[no_expose]
def torusReducedFreeAbelianIso :
    (sheafifiedReducedFreeAbelian.{u + 1} Cₖ Jₖ).obj (liftedPointedTorus k) ≅
      (SimplicialObject.const (Sheaf Jₖ AddCommGrpCat.{u + 1})).obj
        (relativeSource.{u + 1} Jₖ (torusOne Sₖ)) :=
  PreservesCokernel.iso (simplicialSheafification k)
      ((freeAbelian.{u + 1} Cₖ).map (liftedPointedTorus k).hom) ≪≫
    torusBasepointCokernelIso k ≪≫
    (PreservesCokernel.iso (SimplicialObject.const (Sheaf Jₖ AddCommGrpCat.{u + 1}))
      ((freeYoneda.{u + 1} Jₖ).map (torusOne Sₖ))).symm

private theorem sheafifiedReduction_torusReducedFreeAbelianIso_hom :
    (simplicialSheafification k).map (reduction.{u + 1} Cₖ (liftedPointedTorus k)) ≫
      (torusReducedFreeAbelianIso k).hom =
        (freeAbelianSheafLiftedYonedaIso k).hom.app (multiplicativeGroupObject Sₖ) ≫
          (SimplicialObject.const (Sheaf Jₖ AddCommGrpCat.{u + 1})).map
            (relativeSourceπ.{u + 1} Jₖ (torusOne Sₖ)) := by
  let P := simplicialSheafification k
  let F := SimplicialObject.const (Sheaf Jₖ AddCommGrpCat.{u + 1})
  let f := (freeAbelian.{u + 1} Cₖ).map (liftedPointedTorus k).hom
  let g := (freeYoneda.{u + 1} Jₖ).map (torusOne Sₖ)
  let c := torusBasepointCokernelIso k
  let q := PreservesCokernel.iso F g
  let d := (freeAbelianSheafLiftedYonedaIso k).hom.app (multiplicativeGroupObject Sₖ)
  have hc : cokernel.π (P.map f) ≫ c.hom = d ≫ cokernel.π (F.map g) :=
    cokernel.π_desc _ _ _
  have hq : cokernel.π (F.map g) ≫ q.inv = F.map (cokernel.π g) := by
    rw [show q.inv = cokernelComparison g F from PreservesCokernel.iso_inv F g]
    exact π_comp_cokernelComparison g F
  change P.map (cokernel.π f) ≫
      ((PreservesCokernel.iso P f).hom ≫ c.hom ≫ q.inv) =
    d ≫ F.map (cokernel.π g)
  rw [PreservesCokernel.π_iso_hom_assoc]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun m => m ≫ q.inv) hc).trans
      ((Category.assoc _ _ _).trans (congrArg (fun m => d ≫ m) hq)))

/-- The comparison takes the original reduction to the native relative quotient in each degree. -/
theorem sheafifiedReduction_torusReducedFreeAbelianIso_hom_app (n : SimplexCategoryᵒᵖ) :
    (((Functor.whiskeringRight _ _ _).obj (presheafToSheaf Jₖ AddCommGrpCat.{u + 1})).map
        (reduction.{u + 1} Cₖ (liftedPointedTorus k))).app n ≫
        (torusReducedFreeAbelianIso k).hom.app n =
      relativeSourceπ.{u + 1} Jₖ (torusOne Sₖ) := by
  have h := congrArg (fun t => t.app n) (sheafifiedReduction_torusReducedFreeAbelianIso_hom k)
  change _ = ((freeAbelianSheafLiftedYonedaIso k).hom.app
    (multiplicativeGroupObject Sₖ)).app n ≫ relativeSourceπ.{u + 1} Jₖ (torusOne Sₖ) at h
  have hi : ((freeAbelianSheafLiftedYonedaIso k).hom.app
      (multiplicativeGroupObject Sₖ)).app n =
        𝟙 ((freeYoneda.{u + 1} Jₖ).obj (multiplicativeGroupObject Sₖ)) := by
    simp [freeAbelianSheafLiftedYonedaIso]
    rfl
  exact h.trans ((congrArg (fun f => f ≫ relativeSourceπ.{u + 1} Jₖ (torusOne Sₖ)) hi).trans
    (Category.id_comp _))

/-- The actual reduced cochains of the pointed torus are the relative source in degree zero. -/
@[no_expose]
def torusReducedCochainsIso :
    (reducedCochains.{u + 1} Cₖ Jₖ).obj (liftedPointedTorus k) ≅
      (CochainComplex.singleFunctor (Sheaf Jₖ AddCommGrpCat.{u + 1}) 0).obj
        (relativeSource.{u + 1} Jₖ (torusOne Sₖ)) :=
  let A := Sheaf Jₖ AddCommGrpCat.{u + 1}
  let e := ComplexShape.embeddingUpIntLE 0
  let L := relativeSource.{u + 1} Jₖ (torusOne Sₖ)
  (e.extendFunctor A).mapIso
      ((AlgebraicTopology.normalizedMooreComplex A).mapIso (torusReducedFreeAbelianIso k) ≪≫
        (normalizedConstIsoSingle A).app L) ≪≫
    HomologicalComplex.extendSingleIso e L 0 0 rfl

variable [HasDerivedCategory.{d}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Localize the actual cochain comparison in the original derived category. -/
@[no_expose]
def torusReducedDerivedChainsIso :
    (reducedDerivedChains.{d, u + 1} Cₖ Jₖ).obj (liftedPointedTorus k) ≅
      (DerivedCategory.singleFunctor.{d} (Sheaf Jₖ AddCommGrpCat.{u + 1}) 0).obj
        (relativeSource.{u + 1} Jₖ (torusOne Sₖ)) :=
  DerivedCategory.Q.{d}.mapIso (torusReducedCochainsIso k) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ.{d} (Sheaf Jₖ AddCommGrpCat.{u + 1}) 0).app _).symm

/-- The actual reduced motivic class of the positive coordinate on the pointed torus. -/
@[no_expose, colib_tag "COL-1034", colib_ref "Voevodsky2003ReducedPowers"
  "Section 2, before (2.8) and equation (2.9), p. 5"
  "adaptation" "The integral torus class in the native reduced-chain model"]
def torusCoordinateReducedMotivicClass :
    (reducedHypercohomology.{d, u + 1} Cₖ Jₖ (motivicSheafComplex k 1) 1).obj
      (op (liftedPointedTorus k)) :=
  (torusReducedDerivedChainsIso.{d} k).hom ≫ torusCoordinateRelativeMotivicClass.{d} k

/-- The geometric weight-one comparison reads the reduced class as its relative unit. -/
@[colib_tag "COL-1034", reassoc]
theorem torusCoordinateReducedMotivicClass_comp_weightOneDerivedUnitsIso :
    torusCoordinateReducedMotivicClass.{d} k ≫ (weightOneDerivedUnitsIso.{d} k).hom =
      (torusReducedDerivedChainsIso.{d} k).hom ≫
        (DerivedCategory.singleFunctor.{d} (Sheaf Jₖ AddCommGrpCat.{u + 1}) 0).map
          (torusCoordinateRelativeUnit k) := by
  rw [torusCoordinateReducedMotivicClass, Category.assoc,
    torusCoordinateRelativeMotivicClass_comp_weightOneDerivedUnitsIso]

end AlgebraicGeometry.MotivicHomotopy
