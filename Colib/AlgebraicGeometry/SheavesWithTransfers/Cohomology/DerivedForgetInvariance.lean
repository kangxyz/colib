/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.A1InvariantDerivedHom
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.DerivedAdjunction
import Colib.Algebra.Homology.DerivedCategory.SingleKInjective
import Colib.Algebra.Homology.HomotopyCategory.CorepresentedPrecomposition
import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.ObjectProperty
import Colib.CategoryTheory.Preadditive.AdditiveFunctorAbelian
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion

/-!
# A¹-invariance of the cohomology of derived transfer sections

The right-derived underlying presheaf is computed on the same
K-injective complex. Exact presheaf evaluation identifies its
cohomology with shifted Hom from the corresponding smooth
representable. This identification preserves the affine projection.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme SmoothSite.Contraction
open Stacks.Cohomology.Corepresented Stacks.Injectives.KInjectiveResolution

universe u w w'

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "c" => ComplexShape.up ℤ
local notation "U" => SheafWithTransfers.forget k
local notation "R" => transferRepresentable k
local notation "S" => Spec (CommRingCat.of k)

omit [HasDerivedCategory PST] [HasDerivedCategory NST] in
private abbrev evaluationOfTransferPresheaf (X : Cor k) : PST ⥤ AddCommGrpCat.{u + 1} :=
  PresheafWithTransfers.forget ⋙ (CategoryTheory.evaluation _ AddCommGrpCat).obj (op X)

omit [HasDerivedCategory PST] [HasDerivedCategory NST] in
private abbrev evaluationOfTransferSheaf (X : Cor k) : NST ⥤ AddCommGrpCat.{u + 1} :=
  (U) ⋙ evaluationOfTransferPresheaf k X

omit [HasDerivedCategory PST] [HasDerivedCategory NST] in
private def evaluationTransferIso (X : Cor k) :
    preadditiveCoyoneda.obj (op ((R).obj X)) ≅ evaluationOfTransferSheaf k X :=
  NatIso.ofComponents (fun F => (transferSectionsEquiv k X F).toAddCommGrpIso)
    (fun f => by
      ext a
      exact transferSectionsEquiv_comp k X a f)

omit [HasDerivedCategory PST] [HasDerivedCategory NST] in
private abbrev evaluationPresheafRestriction {X Y : Cor k} (a : X ⟶ Y) :
    evaluationOfTransferPresheaf k Y ⟶ evaluationOfTransferPresheaf k X :=
  Functor.whiskerLeft PresheafWithTransfers.forget
    ((CategoryTheory.evaluation _ AddCommGrpCat).map a.op)

omit [HasDerivedCategory PST] [HasDerivedCategory NST] in
private abbrev evaluationRestriction {X Y : Cor k} (a : X ⟶ Y) :
    evaluationOfTransferSheaf k Y ⟶ evaluationOfTransferSheaf k X :=
  Functor.whiskerLeft (U) (evaluationPresheafRestriction k a)

omit [HasDerivedCategory PST] [HasDerivedCategory NST] in
private theorem evaluationTransferIso_naturality {X Y : Cor k} (a : X ⟶ Y) :
    (evaluationTransferIso k Y).hom ≫ evaluationRestriction k a =
      preadditiveCoyoneda.map ((R).map a).op ≫ (evaluationTransferIso k X).hom := by
  apply NatTrans.ext
  funext F
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro (g : (R).obj Y ⟶ F)
  exact (transferSectionsEquiv_naturality_left k F a g).symm

omit [HasDerivedCategory PST] in
private def evaluationDerivedHomEquiv (X : Cor k) (I : CochainComplex NST ℤ)
    [I.IsKInjective] (p : ℤ) :
    (((evaluationOfTransferSheaf k X).mapHomologicalComplex c).obj I).homology p ≃+
      ((transferDerivedHomPresheaf k p).obj (DerivedCategory.Q.obj I)).obj (op X) :=
  let T := evaluationOfTransferSheaf k X
  let e := evaluationTransferIso k X
  let : T.Additive := Functor.additive_of_iso e
  (corepresentedHomologyHomotopyAddEquiv T ((R).obj X) e I p).trans
    (singleKInjectiveHomAddEquiv ((R).obj X) I p)

omit [HasDerivedCategory PST] in
private theorem evaluationDerivedHomEquiv_naturality {X Y : Cor k} (a : X ⟶ Y)
    (I : CochainComplex NST ℤ) [I.IsKInjective] (p : ℤ)
    (x : (((evaluationOfTransferSheaf k Y).mapHomologicalComplex c).obj I).homology p) :
    evaluationDerivedHomEquiv k X I p
        (HomologicalComplex.homologyMap
          (((evaluationRestriction k a).mapHomologicalComplex c).app I) p x) =
      ((transferDerivedHomPresheaf k p).obj (DerivedCategory.Q.obj I)).map a.op
        (evaluationDerivedHomEquiv k Y I p x) := by
  let e := singleKInjectiveHomAddEquiv ((R).obj X) I p
  let eX := evaluationTransferIso k X
  let eY := evaluationTransferIso k Y
  let : (evaluationOfTransferSheaf k X).Additive := Functor.additive_of_iso eX
  let : (evaluationOfTransferSheaf k Y).Additive := Functor.additive_of_iso eY
  let b := corepresentedHomologyHomotopyAddEquiv _ ((R).obj Y) eY I p x
  have h := corepresentedHomologyHomotopyAddEquiv_precomp
    eY eX ((R).map a)
    (evaluationRestriction k a) (evaluationTransferIso_naturality k a) I p x
  exact (congrArg e h).trans (singleKInjectiveHomAddEquiv_precomp ((R).map a) I p b)

omit [HasDerivedCategory PST] [HasDerivedCategory NST] in
private def underlyingHomologyIso (L : CochainComplex PST ℤ) (p : ℤ) (X : Cor k) :
    (((evaluationOfTransferPresheaf k X).mapHomologicalComplex c).obj L).homology p ≅
      (evaluationOfTransferPresheaf k X).obj (L.homology p) :=
  (L.sc p).mapHomologyIso (evaluationOfTransferPresheaf k X)

omit [HasDerivedCategory PST] [HasDerivedCategory NST] in
private theorem underlyingHomologyIso_naturality
    (L : CochainComplex PST ℤ) (p : ℤ) {X Y : Cor k} (a : X ⟶ Y) :
    HomologicalComplex.homologyMap
        (((evaluationPresheafRestriction k a).mapHomologicalComplex c).app L) p ≫
        (underlyingHomologyIso k L p X).hom =
      (underlyingHomologyIso k L p Y).hom ≫
        (evaluationPresheafRestriction k a).app (L.homology p) := by
  exact congr_app (Stacks.Homology.exactHomologyIso_hom_naturality
    (evaluationPresheafRestriction k a) p) L

variable [PerfectField k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})]

omit [HasDerivedCategory PST] in
private theorem isA1Invariant_homology_forget_of_isKInjective
    (I : CochainComplex NST ℤ) [I.IsKInjective] (b : ℤ) (hb : (DerivedCategory.Q.obj I).IsLE b)
    (h : ∀ p, ((DerivedCategory.homologyFunctor NST p).obj
      (DerivedCategory.Q.obj I)).obj.IsA1Invariant)
    (p : ℤ) : ((((U).mapHomologicalComplex c).obj I).homology p).IsA1Invariant := by
  intro X
  let Y := affineLineCylinder.obj X
  let f := (projection (SmoothSite.additiveGroupObject S)).app X
  let a := (Cor.graphFunctor k).map f
  let H := (transferDerivedHomPresheaf k p).obj (DerivedCategory.Q.obj I)
  let L := ((U).mapHomologicalComplex c).obj I
  let g := HomologicalComplex.homologyMap
    (((evaluationRestriction k a).mapHomologicalComplex c).app I) p
  let eX := evaluationDerivedHomEquiv k (Cor.mk X) I p
  let eY := evaluationDerivedHomEquiv k (Cor.mk Y) I p
  have hg : IsIso g := (ConcreteCategory.isIso_iff_bijective _).2 (by
    have hc : eY ∘ g = H.map a.op ∘ eX :=
      funext (evaluationDerivedHomEquiv_naturality k a I p)
    have hR := (ConcreteCategory.isIso_iff_bijective _).1
      (isIso_transferDerivedHomPresheaf_projection k X (DerivedCategory.Q.obj I) b hb h p)
    apply (Function.Bijective.of_comp_iff' eY.bijective g).1
    rw [hc]
    exact hR.comp eX.bijective)
  let e := underlyingHomologyIso k L p (Cor.mk X)
  let d := underlyingHomologyIso k L p (Cor.mk Y)
  let z := PresheafWithTransfers.transfer (L.homology p) a
  have hcomp : g ≫ d.hom = e.hom ≫ z := underlyingHomologyIso_naturality k L p a
  let : IsIso (e.hom ≫ z) := hcomp ▸ IsIso.comp_isIso' hg d.isIso_hom
  exact IsIso.of_isIso_comp_left e.hom z

/-- The original total right-derived underlying presheaf of a bounded-above
effective transfer complex has A¹-invariant cohomology in every degree. -/
theorem isA1Invariant_homology_forgetDerived
    (K : DerivedCategory NST) (b : ℤ) (hb : K.IsLE b)
    (h : ∀ p, ((DerivedCategory.homologyFunctor NST p).obj K).obj.IsA1Invariant) (p : ℤ) :
    ((DerivedCategory.homologyFunctor PST p).obj
      ((forgetDerivedFunctor k).obj K)).IsA1Invariant := by
  let J := (DerivedCategory.Q (C := NST)).objPreimage K
  obtain ⟨I, f, hI, hf⟩ :=
    Stacks.Injectives.exists_kInjective_resolution_of_grothendieck J
  let : I.IsKInjective := hI
  let : QuasiIso f := hf
  let e : (DerivedCategory.Q (C := NST)).obj I ≅ K :=
    (asIso (DerivedCategory.Q.map f)).symm ≪≫ (DerivedCategory.Q (C := NST)).objObjPreimageIso K
  let : K.IsLE b := hb
  have hb' : (DerivedCategory.Q.obj I).IsLE b := DerivedCategory.TStructure.t.isLE_of_iso e.symm b
  have h' (q : ℤ) :
      ((DerivedCategory.homologyFunctor NST q).obj (DerivedCategory.Q.obj I)).obj.IsA1Invariant :=
    (h q).of_iso ((U).mapIso ((DerivedCategory.homologyFunctor NST q).mapIso e.symm))
  let : IsIso ((forgetDerivedUnit k).app I) :=
    isIso_app_of_isKInjective (DerivedCategory.Q (C := NST)) _ _
      (invertsQuasiIso_mapHomologicalComplex_comp_Q (U)) I hI
  let H := DerivedCategory.homologyFunctor PST p
  let d := ((DerivedCategory.homologyFunctorFactors PST p).app
    (((U).mapHomologicalComplex c).obj I)).symm ≪≫
      H.mapIso (asIso ((forgetDerivedUnit k).app I) ≪≫ (forgetDerivedFunctor k).mapIso e)
  exact (isA1Invariant_homology_forget_of_isKInjective k I b hb' h' p).of_iso d

end AlgebraicGeometry.SheafWithTransfers
