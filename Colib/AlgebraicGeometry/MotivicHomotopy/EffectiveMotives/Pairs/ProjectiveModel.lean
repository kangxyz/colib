/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Basic
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.OpenSequence
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.NisnevichSingleCoproduct
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.ReducedProjective
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.RepresentableUnit
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel.Triangulated
public import Colib.Algebra.Homology.MappingCone.ShortExact
import Colib.Algebra.Homology.CochainComplex.SplitFactorization.AdditiveMap
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-!
# Projective representatives of open pairs

Use the cone of the actual graph between projective transfer representables.
After sheafification its augmentation is the original relative quotient,
and naturality holds for maps of pairs before passage to motives.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sm(" K ")" => SmoothSite (Spec (CommRingCat.of K))
local notation "PST(" K ")" => LargePresheaves K
local notation "NST(" K ")" => LargeSheaves K
local notation "c" => ComplexShape.up ℤ

/-- The canonical abelian structure on sheaves with transfers. -/
local instance projectivePairModelAbelian : Abelian NST(k) := SheafWithTransfers.abelian k

/-- The original signed graph of a smooth scheme, placed in degree zero
in projective transfer presheaves. -/
abbrev projectiveSmoothSingle : Sm(k) ⥤ CochainComplex PST(k) ℤ :=
  Cor.graphFunctor k ⋙ representableLarge k ⋙ CochainComplex.singleFunctor PST(k) 0

/-- The graph arrow, as a natural map of the two actual endpoint complexes. -/
def projectivePairArrow :
    Arrow.leftFunc ⋙ projectiveSmoothSingle k ⟶ Arrow.rightFunc ⋙ projectiveSmoothSingle k where
  app j := (projectiveSmoothSingle k).map j.hom
  naturality {i j} φ := by
    change (projectiveSmoothSingle k).map φ.left ≫ (projectiveSmoothSingle k).map j.hom =
      (projectiveSmoothSingle k).map i.hom ≫ (projectiveSmoothSingle k).map φ.right
    rw [← Functor.map_comp, ← Functor.map_comp, Arrow.w φ]

/-- The cone of the original projective graph arrow, functorial in the actual pairs. -/
abbrev projectivePairCochain : Arrow Sm(k) ⥤ CochainComplex PST(k) ℤ :=
  CochainComplex.mappingConeNatTransFunctor (projectivePairArrow k)

/-- These literal cones consist of bounded-above projective coefficients. -/
def projectivePairModel : Arrow Sm(k) ⥤ BoundedAboveProjectiveHomotopy k :=
  (boundedAboveProjectiveCondition k).lift
    (projectivePairCochain k ⋙ HomotopyCategory.quotient PST(k) c) (fun j =>
      boundedAboveProjective_mappingCone k ((projectivePairArrow k).app j)
        (projectiveRepresentableSingle k (Cor.mk j.left)).property
        (projectiveRepresentableSingle k (Cor.mk j.right)).property)

local notation "a(" K ")" => nisnevichSheafify K
local notation "s(" K ")" => CochainComplex.singleFunctor NST(K) 0

/-- The transfer quotient sequence of a pair, put in degree zero. -/
abbrev cochainTransferPair (j : Arrow Sm(k)) : ShortComplex (CochainComplex NST(k) ℤ) :=
  (transferPairSequence k j).map (s(k))

/-- The actual signed cone of the localized graph, with its two original components. -/
abbrev cochainTransferPairCone (j : Arrow Sm(k)) :=
  CochainComplex.mappingCone (cochainTransferPair k j).f

/-- A map of relative pairs acts on the original sheaf graph cones term by term. -/
def cochainTransferPairConeMap {i j : Arrow Sm(k)} (φ : i ⟶ j) :
    cochainTransferPairCone k i ⟶ cochainTransferPairCone k j :=
  (CochainComplex.mappingConeNatTransFunctor
    (Arrow.leftToRight (C := CochainComplex NST(k) ℤ))).map
    (ShortComplex.fFunctor.map ((s(k)).mapShortComplex.map (transferPairSequenceMap k φ)))

/-- The cone augmentation commutes with the literal map of quotients. -/
theorem cochainTransferPairConeMap_desc {i j : Arrow Sm(k)} (φ : i ⟶ j) :
    cochainTransferPairConeMap k φ ≫ CochainComplex.mappingCone.descShortComplex
      (cochainTransferPair k j) =
    CochainComplex.mappingCone.descShortComplex (cochainTransferPair k i) ≫
      (s(k)).map ((transferPairCokernelFunctor k).map φ) :=
  CochainComplex.mappingCone.descShortComplex_naturality
    ((s(k)).mapShortComplex.map (transferPairSequenceMap k φ))

/-- Degree zero commutes with sheafification on the original representable. -/
def sheafifiedPairEndpoints (X : Sm(k)) :
    ((a(k)).mapHomologicalComplex c).obj ((projectiveSmoothSingle k).obj X) ≅
      (s(k)).obj ((smoothTransferRepresentable k).obj X) :=
  (HomologicalComplex.singleMapHomologicalComplex (a(k)) c (0 : ℤ)).app
    ((representableLarge k).obj (Cor.mk X))

theorem sheafifiedPairEndpoints_naturality {X Y : Sm(k)} (f : X ⟶ Y) :
    ((a(k)).mapHomologicalComplex c).map ((projectiveSmoothSingle k).map f) ≫
        (sheafifiedPairEndpoints k Y).hom =
      (sheafifiedPairEndpoints k X).hom ≫
        (s(k)).map ((smoothTransferRepresentable k).map f) :=
  (HomologicalComplex.singleMapHomologicalComplex (a(k)) c (0 : ℤ)).hom.naturality
    ((representableLarge k).map ((Cor.graphFunctor k).map f))

/-- The termwise sheafification comparison for the chosen literal cone. -/
def sheafifiedPairConeIso (j : Arrow Sm(k)) :
    ((a(k)).mapHomologicalComplex c).obj ((projectivePairCochain k).obj j) ≅
      CochainComplex.mappingCone (cochainTransferPair k j).f := by
  let f := (projectivePairArrow k).app j
  let g := ((a(k)).mapHomologicalComplex c).map f
  let h := (cochainTransferPair k j).f
  let e₁ := sheafifiedPairEndpoints k j.left
  let e₂ := sheafifiedPairEndpoints k j.right
  have he : e₁.hom ≫ h = g ≫ e₂.hom :=
    (sheafifiedPairEndpoints_naturality k j.hom).symm
  let e : Arrow.mk g ≅ Arrow.mk h := Arrow.isoMk e₁ e₂ he
  let F := CochainComplex.mappingConeNatTransFunctor
    (Arrow.leftToRight (C := CochainComplex NST(k) ℤ))
  exact CochainComplex.mappingCone.mapHomologicalComplexIso f (a(k)) ≪≫ F.mapIso e

set_option maxHeartbeats 1200000 in
-- Pin the two sources of functoriality before comparing the actual cone maps.
/-- Sheafification takes the original pair cone map to the literal transfer cone map. -/
theorem sheafifiedPairConeIso_naturality {i j : Arrow Sm(k)} (φ : i ⟶ j) :
    ((a(k)).mapHomologicalComplex c).map ((projectivePairCochain k).map φ) ≫
        (sheafifiedPairConeIso k j).hom =
      (sheafifiedPairConeIso k i).hom ≫ cochainTransferPairConeMap k φ := by
  let A := (a(k)).mapHomologicalComplex c
  let F := CochainComplex.mappingConeNatTransFunctor
    (Arrow.leftToRight (C := CochainComplex NST(k) ℤ))
  let e (b : Arrow Sm(k)) :
      Arrow.mk (A.map ((projectivePairArrow k).app b)) ≅ Arrow.mk (cochainTransferPair k b).f :=
    Arrow.isoMk (sheafifiedPairEndpoints k b.left) (sheafifiedPairEndpoints k b.right)
      (sheafifiedPairEndpoints_naturality k b.hom).symm
  let u := Arrow.homMk' ((projectiveSmoothSingle k).map φ.left)
    ((projectiveSmoothSingle k).map φ.right) ((projectivePairArrow k).naturality φ)
  let v := ShortComplex.fFunctor.map
    ((s(k)).mapShortComplex.map (transferPairSequenceMap k φ))
  have h : A.mapArrow.map u ≫ (e j).hom = (e i).hom ≫ v := by
    apply Arrow.hom_ext
    · exact sheafifiedPairEndpoints_naturality k φ.left
    · exact sheafifiedPairEndpoints_naturality k φ.right
  change A.map ((projectivePairCochain k).map φ) ≫
      (CochainComplex.mappingCone.mapHomologicalComplexIso _ (a(k))).hom ≫ F.map (e j).hom =
    ((CochainComplex.mappingCone.mapHomologicalComplexIso _ (a(k))).hom ≫ F.map (e i).hom) ≫
      F.map v
  have ha := CochainComplex.SplitFactorization.coneMapIso_naturality (a(k))
    ((projectivePairArrow k).app i) ((projectivePairArrow k).app j)
    ((projectiveSmoothSingle k).map φ.left) ((projectiveSmoothSingle k).map φ.right)
    ((projectivePairArrow k).naturality φ).symm
  change A.map ((projectivePairCochain k).map φ) ≫
      (CochainComplex.mappingCone.mapHomologicalComplexIso _ (a(k))).hom =
    (CochainComplex.mappingCone.mapHomologicalComplexIso _ (a(k))).hom ≫
      F.map (A.mapArrow.map u) at ha
  rw [← Category.assoc, ha, Category.assoc, Category.assoc, ← F.map_comp, ← F.map_comp, h]
  rfl

variable [HasDerivedCategory.{w} PST(k)] [HasDerivedCategory.{w'} NST(k)]

local notation "Q(" K ")" => (DerivedCategory.Q : CochainComplex NST(K) ℤ ⥤ DerivedCategory NST(K))

/-- The actual cochain model of the pair in the presheaf derived category. -/
abbrev projectivePairDerived : Arrow Sm(k) ⥤ DerivedCategory.Minus PST(k) :=
  projectivePairModel k ⋙ projectiveHomotopyToDerivedMinus k

/-- The derived Nisnevich sheafification of the literal projective cone
has the original transfer sheaf quotient as its canonical augmentation. -/
def projectivePairDerivedAugmentation (j : Arrow Sm(k)) :
    (derivedNisnevichSheafification k).obj ((projectivePairDerived k).obj j) ⟶
      (singleTransferSheafMinus k).obj ((transferPairCokernelFunctor k).obj j) := by
  let A := a(k)
  let K := (projectivePairCochain k).obj j
  let e := (DerivedCategory.quotientCompQhIso PST(k)).app K
  let f := CochainComplex.mappingCone.descShortComplex (cochainTransferPair k j)
  exact ObjectProperty.homMk (A.mapDerivedCategory.map e.hom ≫
    A.mapDerivedCategoryFactors.hom.app K ≫
    (Q(k)).map ((sheafifiedPairConeIso k j).hom ≫ f))

/-- The augmentation of a literal pair commutes with the original map on its quotient. -/
@[reassoc]
theorem projectivePairDerivedAugmentation_naturality {i j : Arrow Sm(k)} (φ : i ⟶ j) :
    (derivedNisnevichSheafification k).map ((projectivePairDerived k).map φ) ≫
        projectivePairDerivedAugmentation k j =
      projectivePairDerivedAugmentation k i ≫
        (singleTransferSheafMinus k).map ((transferPairCokernelFunctor k).map φ) := by
  apply ObjectProperty.hom_ext
  let A := a(k)
  let e := DerivedCategory.quotientCompQhIso PST(k)
  let f := (projectivePairCochain k).map φ
  let q (b : Arrow Sm(k)) := CochainComplex.mappingCone.descShortComplex (cochainTransferPair k b)
  let g := (s(k)).map ((transferPairCokernelFunctor k).map φ)
  change A.mapDerivedCategory.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ c).map f)) ≫
      A.mapDerivedCategory.map (e.hom.app _) ≫ A.mapDerivedCategoryFactors.hom.app _ ≫
        (Q(k)).map ((sheafifiedPairConeIso k j).hom ≫ q j) =
    (A.mapDerivedCategory.map (e.hom.app _) ≫ A.mapDerivedCategoryFactors.hom.app _ ≫
        (Q(k)).map ((sheafifiedPairConeIso k i).hom ≫ q i)) ≫ (Q(k)).map g
  have he := e.hom.naturality f
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ c).map f) ≫ e.hom.app _ =
    e.hom.app _ ≫ DerivedCategory.Q.map f at he
  have he' := congrArg A.mapDerivedCategory.map he
  rw [A.mapDerivedCategory.map_comp, A.mapDerivedCategory.map_comp] at he'
  simp only [← Category.assoc, reassoc_of% he']
  rw [Category.assoc (A.mapDerivedCategory.map (e.hom.app _)),
    A.mapDerivedCategoryFactors_hom_naturality f]
  simp only [Category.assoc, ← (Q(k)).map_comp]
  have hc : (A.mapHomologicalComplex c).map f ≫ (sheafifiedPairConeIso k j).hom ≫ q j =
      (sheafifiedPairConeIso k i).hom ≫ q i ≫ g := by
    rw [← Category.assoc, sheafifiedPairConeIso_naturality, Category.assoc]
    exact congrArg ((sheafifiedPairConeIso k i).hom ≫ ·) (cochainTransferPairConeMap_desc k φ)
  exact congrArg
    (fun h => A.mapDerivedCategory.map (e.hom.app ((projectivePairCochain k).obj i)) ≫
      A.mapDerivedCategoryFactors.hom.app ((projectivePairCochain k).obj i) ≫ (Q(k)).map h) hc


/-- For a literal open pair the augmentation is an isomorphism:
the sheafified graph is mono and the target is its actual cokernel. -/
instance isIso_projectivePairDerivedAugmentation {U X : Sm(k)} (j : U ⟶ X)
    [IsOpenImmersion j.left] :
    IsIso (projectivePairDerivedAugmentation k (Arrow.mk j)) := by
  let K := (projectivePairCochain k).obj (Arrow.mk j)
  let e := (DerivedCategory.quotientCompQhIso PST(k)).app K
  let b := sheafifiedPairConeIso k (Arrow.mk j)
  let S := cochainTransferPair k (Arrow.mk j)
  let f := CochainComplex.mappingCone.descShortComplex S
  have hS : S.ShortExact := (transferPairSequence_shortExact k j).map_of_exact (s(k))
  have hf : QuasiIso f := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  let : IsIso ((Q(k)).map f) := (DerivedCategory.isIso_Q_map_iff_quasiIso NST(k) f).2 hf
  let I : DerivedCategory.Minus NST(k) ⥤ DerivedCategory NST(k) := DerivedCategory.Minus.ι
  let ψ := projectivePairDerivedAugmentation k (Arrow.mk j)
  have h : IsIso (I.map ψ) := by
    change IsIso ((a(k)).mapDerivedCategory.map e.hom ≫
      (a(k)).mapDerivedCategoryFactors.hom.app K ≫ (Q(k)).map (b.hom ≫ f))
    rw [(Q(k)).map_comp]
    infer_instance
  exact isIso_of_reflects_iso ψ I

/-- Compute a projective coefficient functor on the original pair cone,
then apply the actual exact Nisnevich sheafification. -/
def projectivePairTermwiseModelIso (F : PST(k) ⥤ PST(k)) [F.Additive] (j : Arrow Sm(k)) :
    ((projectiveDerivedMinusFunctor k F ⋙ derivedNisnevichSheafification k).obj
      ((projectivePairDerived k).obj j)).obj ≅
        (Q(k)).obj
          (((F ⋙ a(k)).mapHomologicalComplex c).obj ((projectivePairCochain k).obj j)) := by
  let K := (projectivePairCochain k).obj j
  let P := (projectivePairModel k).obj j
  let E := boundedAboveProjectiveEquivalence k
  let I : DerivedCategory.Minus NST(k) ⥤ DerivedCategory NST(k) := DerivedCategory.Minus.ι
  let H := projectiveHomotopyMapToDerivedMinus k F
  let e := (derivedNisnevichSheafification k ⋙ I).mapIso (H.mapIso (E.unitIso.app P).symm)
  exact e ≪≫ (a(k)).mapDerivedCategoryFactorsh.app ((F.mapHomotopyCategory c).obj P.obj) ≪≫
    (DerivedCategory.quotientCompQhIso NST(k)).app (((F ⋙ a(k)).mapHomologicalComplex c).obj K)

/-- The original chain map representing a coefficient natural transformation
on the chosen cone is the termwise map of that transformation. -/
@[reassoc]
theorem projectivePairTermwiseModelIso_coefficient {F G : PST(k) ⥤ PST(k)}
    [F.Additive] [G.Additive] (η : F ⟶ G) (j : Arrow Sm(k)) :
    ((derivedNisnevichSheafification k).map
        ((projectiveCoefficientNatTrans k η).app ((projectivePairDerived k).obj j))).hom ≫
      (projectivePairTermwiseModelIso k G j).hom =
      (projectivePairTermwiseModelIso k F j).hom ≫
        (Q(k)).map (((Functor.whiskerRight η (a(k))).mapHomologicalComplex c).app
          ((projectivePairCochain k).obj j)) := by
  let A := a(k)
  let K := (projectivePairCochain k).obj j
  let P := (projectivePairModel k).obj j
  let E := boundedAboveProjectiveEquivalence k
  let P' := E.inverse.obj (E.functor.obj P)
  let e : P' ⟶ P := E.unitIso.inv.app P
  let d := A.mapDerivedCategory
  let B := A.mapHomotopyCategory c
  let Fh := F.mapHomotopyCategory c
  let Gh := G.mapHomotopyCategory c
  let q : HomotopyCategory PST(k) c ⥤ DerivedCategory PST(k) := DerivedCategory.Qh
  let r : HomotopyCategory NST(k) c ⥤ DerivedCategory NST(k) := DerivedCategory.Qh
  let τ := η.mapHomotopyCategory c
  let b := A.mapDerivedCategoryFactorsh
  let l := DerivedCategory.quotientCompQhIso NST(k)
  let ψ := ((Functor.whiskerRight η A).mapHomologicalComplex c).app K
  let KF := ((F ⋙ A).mapHomologicalComplex c).obj K
  let KG := ((G ⋙ A).mapHomologicalComplex c).obj K
  have h₁ : τ.app P'.obj ≫ Gh.map e.hom = Fh.map e.hom ≫ τ.app P.obj :=
    (τ.naturality e.hom).symm
  have h₂ : d.map (q.map (τ.app P.obj)) ≫ b.hom.app (Gh.obj P.obj) =
      b.hom.app (Fh.obj P.obj) ≫ r.map (B.map (τ.app P.obj)) :=
    b.hom.naturality (τ.app P.obj)
  have h₃ : r.map (B.map (τ.app P.obj)) ≫ l.hom.app KG =
      l.hom.app KF ≫ (Q(k)).map ψ := by
    change r.map ((HomotopyCategory.quotient _ c).map ψ) ≫ l.hom.app KG = _
    exact DerivedCategory.quotientCompQhIso_hom_naturality ψ
  have h₄ : ((derivedNisnevichSheafification k).map
      ((projectiveCoefficientNatTrans k η).app ((projectivePairDerived k).obj j))).hom =
        d.map (q.map (τ.app P'.obj)) := by
    change d.map (((projectiveCoefficientNatTrans k η).app ((projectivePairDerived k).obj j)).hom)
      = _
    rw [projectiveCoefficientNatTrans_app_hom]
    rfl
  rw [h₄]
  change d.map (q.map (τ.app P'.obj)) ≫
      (d.map (q.map (Gh.map e.hom)) ≫ b.hom.app (Gh.obj P.obj) ≫ l.hom.app KG) =
    (d.map (q.map (Fh.map e.hom)) ≫ b.hom.app (Fh.obj P.obj) ≫ l.hom.app KF) ≫
      (Q(k)).map ψ
  rw [← Category.assoc, ← d.map_comp, ← q.map_comp, h₁, q.map_comp, d.map_comp,
    Category.assoc, Category.assoc, Category.assoc, reassoc_of% h₂, h₃]

/-- Termwise computation of a projective coefficient functor is compatible
with the actual maps between pair models. -/
theorem projectivePairTermwiseModelIso_naturality (F : PST(k) ⥤ PST(k))
    [F.Additive] {i j : Arrow Sm(k)} (φ : i ⟶ j) :
    ((projectiveDerivedMinusFunctor k F ⋙ derivedNisnevichSheafification k).map
      ((projectivePairDerived k).map φ)).hom ≫ (projectivePairTermwiseModelIso k F j).hom =
      (projectivePairTermwiseModelIso k F i).hom ≫
        (Q(k)).map (((F ⋙ a(k)).mapHomologicalComplex c).map
          ((projectivePairCochain k).map φ)) := by
  let A := a(k)
  let K (X : Arrow Sm(k)) := (projectivePairCochain k).obj X
  let P (X : Arrow Sm(k)) := (projectivePairModel k).obj X
  let E := boundedAboveProjectiveEquivalence k
  let h : P i ⟶ P j := (projectivePairModel k).map φ
  let hi := E.unitIso.inv.app (P i)
  let hj := E.unitIso.inv.app (P j)
  let B := F.mapHomotopyCategory c
  let d := A.mapDerivedCategory
  let q : HomotopyCategory PST(k) c ⥤ DerivedCategory PST(k) := DerivedCategory.Qh
  let l : HomotopyCategory NST(k) c ⥤ DerivedCategory NST(k) := DerivedCategory.Qh
  let f := B.map h.hom
  let t := A.mapDerivedCategoryFactorsh
  let z := DerivedCategory.quotientCompQhIso NST(k)
  let g := ((F ⋙ A).mapHomologicalComplex c).map ((projectivePairCochain k).map φ)
  have hh : (E.inverse.map (E.functor.map h)).hom ≫ hj.hom = hi.hom ≫ h.hom := by
    exact congrArg (fun x => x.hom) (E.unitIso.inv.naturality h)
  have hb : B.map ((E.inverse.map (E.functor.map h)).hom) ≫ B.map hj.hom =
      B.map hi.hom ≫ f := by
    rw [← B.map_comp, ← B.map_comp, hh]
  have ht : d.map (q.map f) ≫ t.hom.app (B.obj (P j).obj) =
      t.hom.app (B.obj (P i).obj) ≫ l.map ((A.mapHomotopyCategory c).map f) :=
    t.hom.naturality f
  have hz : l.map ((A.mapHomotopyCategory c).map f) ≫ z.hom.app _ =
      z.hom.app _ ≫ (Q(k)).map g := by
    change l.map ((HomotopyCategory.quotient _ c).map g) ≫ _ = _
    exact DerivedCategory.quotientCompQhIso_hom_naturality g
  change d.map (q.map (B.map ((E.inverse.map (E.functor.map h)).hom))) ≫
      (d.map (q.map (B.map hj.hom)) ≫ t.hom.app (B.obj (P j).obj) ≫ z.hom.app _) =
    (d.map (q.map (B.map hi.hom)) ≫ t.hom.app (B.obj (P i).obj) ≫ z.hom.app _) ≫
      (Q(k)).map g
  rw [← Category.assoc, ← d.map_comp, ← q.map_comp, hb, q.map_comp, d.map_comp,
    Category.assoc, Category.assoc, Category.assoc, reassoc_of% ht, hz]
  rfl

end AlgebraicGeometry.MotivicHomotopy
