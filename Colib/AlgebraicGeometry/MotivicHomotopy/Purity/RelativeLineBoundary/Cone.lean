/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.LaurentDerived
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.ReducedProjectiveRepresentable
import Colib.Algebra.Homology.MappingCone.Augmentation
import all Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.LaurentCochain
import all Colib.AlgebraicGeometry.SheavesWithTransfers.TorusTensor.ReducedProjectiveRepresentable

/-!
# The ambient inclusion into the original projective pair cone

The right inclusion of the literal cone gives the ambient quotient after
augmentation. This holds both before and after applying the actual Laurent
coefficient functor.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k]

local notation "Sm(" K ")" => SmoothSite (Spec (CommRingCat.of K))
local notation "PST(" K ")" => LargePresheaves K
local notation "NST(" K ")" => LargeSheaves K
local notation "G(" K ")" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of K))
local notation "A(" K ")" => nisnevichSheafify K
local notation "L(" K ")" => parameterTensorFunctor G(K)
local notation "Qp(" K ")" => (DerivedCategory.Q : CochainComplex PST(K) ℤ ⥤ DerivedCategory PST(K))
local notation "Qs(" K ")" => (DerivedCategory.Q : CochainComplex NST(K) ℤ ⥤ DerivedCategory NST(K))
local notation "S(" K ")" => singleTransferSheafMinus K
local notation "p(" K ")" => transferPairProjection K

/-- Use the transfer-sheaf abelian structure for the cone of the line inclusion. -/
local instance instAbelianRelativeLineCone : Abelian (NST(k)) := SheafWithTransfers.abelian k

private abbrev ambientCochainMap (j : Arrow Sm(k)) :
    (projectiveSmoothSingle k).obj j.right ⟶ (projectivePairCochain k).obj j :=
  CochainComplex.mappingCone.inr ((projectivePairArrow k).app j)

set_option maxHeartbeats 750000 in
-- Expose the same right endpoint in the two definitions of the cone comparison.
private theorem ambientCochain_sheafified_aug (j : Arrow Sm(k)) :
    ((A(k)).mapHomologicalComplex (.up ℤ)).map (ambientCochainMap k j) ≫
      ((sheafifiedPairConeIso k j).hom ≫
        CochainComplex.mappingCone.descShortComplex (cochainTransferPair k j)) =
      (sheafifiedPairEndpoints k j.right).hom ≫ (cochainTransferPair k j).g := by
  let g := Arrow.mk ((projectivePairArrow k).app j)
  let B := cochainTransferPair k j
  let F := A(k)
  let H := F.mapHomologicalComplex (.up ℤ)
  let P :=
    CochainComplex.mappingConeNatTransFunctor (Arrow.leftToRight (C := CochainComplex NST(k) ℤ))
  let a : H.mapArrow.obj g ⟶ Arrow.mk B.f :=
    Arrow.homMk' (sheafifiedPairEndpoints k j.left).hom (sheafifiedPairEndpoints k j.right).hom
      ((sheafifiedPairEndpoints_naturality k j.hom).symm)
  have h : (sheafifiedPairConeIso k j).hom =
      (CochainComplex.mappingCone.mapHomologicalComplexIso g.hom F).hom ≫ P.map a := by
    unfold sheafifiedPairConeIso sheafifiedPairConeNatIso
    rfl
  rw [h, Category.assoc]
  exact CochainComplex.mappingCone.coneAugmentation_inr F g B a

set_option maxHeartbeats 750000 in
-- The Laurent endpoint is the literal product representable in degree zero.
private theorem ambientCochain_laurent_aug (j : Arrow Sm(k)) :
    ((L(k) ⋙ A(k)).mapHomologicalComplex (.up ℤ)).map (ambientCochainMap k j) ≫
      ((laurentCochainComparison k j).hom ≫ laurentCochainAugmentation k j) =
      (laurentCochainEndpointIso k j.right).hom ≫
        (cochainTransferPair k ((laurentPair k).obj j)).g := by
  let g := Arrow.mk ((projectivePairArrow k).app j)
  let B := cochainTransferPair k ((laurentPair k).obj j)
  let F := L(k) ⋙ A(k)
  let d := (laurentCochainArrowIso k j).hom
  change (F.mapHomologicalComplex (.up ℤ)).map (CochainComplex.mappingCone.inr g.hom) ≫
    ((laurentCochainComparison k j).hom ≫ CochainComplex.mappingCone.descShortComplex B) = _
  rw [laurentCochainComparison_hom, Category.assoc]
  exact CochainComplex.mappingCone.coneAugmentation_inr F g B d

variable [HasDerivedCategory.{w} PST(k)] [HasDerivedCategory.{w'} NST(k)]

/-- The actual ambient degree-zero representable maps to the original
projective cone by the right inclusion. -/
@[no_expose]
def projectivePairAmbientMap (j : Arrow Sm(k)) :
    singleTransferRepresentable k (Cor.mk j.right) ⟶ (projectivePairDerived k).obj j :=
  ObjectProperty.homMk (Qp(k).map (ambientCochainMap k j) ≫
    (DerivedCategory.quotientCompQhIso PST(k)).inv.app ((projectivePairCochain k).obj j))

/-- The original sheafification comparison on the ambient single. -/
@[no_expose]
def projectiveAmbientSingleSheafIso (X : Sm(k)) :
    (derivedNisnevichSheafification k).obj (singleTransferRepresentable k (Cor.mk X)) ≅
      (S(k)).obj ((smoothTransferRepresentable k).obj X) :=
  ObjectProperty.isoMk _ (((A(k)).mapDerivedCategoryFactors.app ((projectiveSmoothSingle k).obj X))
    ≪≫ Qs(k).mapIso (sheafifiedPairEndpoints k X))

/-- The underlying comparison on the ambient single is the actual
sheafification and the degree-zero endpoint comparison. -/
theorem projectiveAmbientSingleSheafIso_hom_hom (X : Sm(k)) :
    (projectiveAmbientSingleSheafIso k X).hom.hom =
      (A(k)).mapDerivedCategoryFactors.hom.app ((projectiveSmoothSingle k).obj X) ≫
        Qs(k).map (sheafifiedPairEndpoints k X).hom := by
  unfold projectiveAmbientSingleSheafIso
  exact Eq.refl _

set_option maxHeartbeats 850000 in
-- Compare the actual augmentation after the native derived right inclusion.
/-- The augmented ambient inclusion is the original transfer quotient map. -/
theorem projectivePairDerivedAugmentation_ambient (j : Arrow Sm(k)) :
    (derivedNisnevichSheafification k).map (projectivePairAmbientMap k j) ≫
        projectivePairDerivedAugmentation k j =
      (projectiveAmbientSingleSheafIso k j.right).hom ≫ (S(k)).map ((p(k)).app j) := by
  apply ObjectProperty.hom_ext
  let L := (projectiveSmoothSingle k).obj j.right
  let K := (projectivePairCochain k).obj j
  let f : L ⟶ K := ambientCochainMap k j
  let d := (A(k)).mapDerivedCategory
  let c := (A(k)).mapDerivedCategoryFactors
  let e := (DerivedCategory.quotientCompQhIso PST(k)).app K
  let x := (sheafifiedPairConeIso k j).hom ≫
    CochainComplex.mappingCone.descShortComplex (cochainTransferPair k j)
  let y := (sheafifiedPairEndpoints k j.right).hom
  let g := (cochainTransferPair k j).g
  have hf : (projectivePairAmbientMap k j).hom ≫ e.hom = Qp(k).map f := by
    change (Qp(k).map f ≫ e.inv) ≫ e.hom = _
    have h := congrArg (Qp(k).map f ≫ ·) e.inv_hom_id
    exact (Category.assoc _ _ _).trans (h.trans (Category.comp_id _))
  have hn : d.map (Qp(k).map f) ≫ c.hom.app K =
      c.hom.app L ≫ Qs(k).map (((A(k)).mapHomologicalComplex (.up ℤ)).map f) :=
    c.hom.naturality f
  change d.map (projectivePairAmbientMap k j).hom ≫
      (d.map e.hom ≫ c.hom.app K ≫ Qs(k).map x) =
    (c.hom.app L ≫ Qs(k).map y) ≫ Qs(k).map g
  calc
    _ = d.map (Qp(k).map f) ≫ c.hom.app K ≫ Qs(k).map x := by
      rw [← Category.assoc (d.map (projectivePairAmbientMap k j).hom), ← d.map_comp, hf]
    _ = c.hom.app L ≫ Qs(k).map
          (((A(k)).mapHomologicalComplex (.up ℤ)).map f ≫ x) := by
      rw [← Category.assoc, hn, Category.assoc, ← (Qs(k)).map_comp]
    _ = (c.hom.app L ≫ Qs(k).map y) ≫ Qs(k).map g := by
      rw [ambientCochain_sheafified_aug k j, (Qs(k)).map_comp, Category.assoc]

private def projectiveAmbientLift (j : Arrow Sm(k)) :
    projectiveRepresentableSingle k (Cor.mk j.right) ⟶ (projectivePairModel k).obj j :=
  ObjectProperty.homMk ((HomotopyCategory.quotient PST(k) (.up ℤ)).map (ambientCochainMap k j))

set_option maxHeartbeats 850000 in
-- Cancel the chosen projective representative by the actual equivalence unit.
omit [HasDerivedCategory NST(k)] in
private theorem chosenProjectivePairAmbient (j : Arrow Sm(k)) :
    let E := boundedAboveProjectiveEquivalence k
    E.inverse.map (projectivePairAmbientMap k j) ≫
      E.unitIso.inv.app ((projectivePairModel k).obj j) =
      (projectiveSingleRepresentativeIso k (Cor.mk j.right)).hom ≫ projectiveAmbientLift k j := by
  intro E
  let Y := Cor.mk j.right
  let P := projectiveRepresentableSingle k Y
  let f := projectiveAmbientLift k j
  let Z := DerivedCategory.quotientCompQhIso PST(k)
  let e : E.functor.obj P ≅ singleTransferRepresentable k Y :=
    ObjectProperty.isoMk _ (Z.app ((projectiveSmoothSingle k).obj j.right))
  have h : projectivePairAmbientMap k j = e.inv ≫ E.functor.map f := by
    apply ObjectProperty.hom_ext
    change Qp(k).map (ambientCochainMap k j) ≫ (Z.app _).inv =
      (Z.app _).inv ≫ DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (.up ℤ)).map (ambientCochainMap k j))
    exact Z.inv.naturality (ambientCochainMap k j)
  have h₀ : (projectiveSingleRepresentativeIso k Y).hom =
      E.inverse.map e.inv ≫ E.unitIso.inv.app P := rfl
  have hn : E.inverse.map (E.functor.map f) ≫ E.unitIso.inv.app ((projectivePairModel k).obj j) =
      E.unitIso.inv.app P ≫ f := E.unitIso.inv.naturality f
  rw [h, E.inverse.map_comp, Category.assoc, hn, ← Category.assoc, h₀]

set_option maxHeartbeats 1100000 in
-- Identify the chosen and literal models before applying their cochain factorization.
private theorem projectivePairTermwiseModelIso_ambient
    (F : PST(k) ⥤ PST(k)) [F.Additive] (j : Arrow Sm(k)) :
    ((projectiveDerivedMinusFunctor k F ⋙ derivedNisnevichSheafification k).map
      (projectivePairAmbientMap k j)).hom ≫ (projectivePairTermwiseModelIso k F j).hom =
      (projectiveSingleTensorModelIso k F (Cor.mk j.right)).hom ≫
        (Qs(k)).map (((F ⋙ A(k)).mapHomologicalComplex (.up ℤ)).map
          (ambientCochainMap k j)) := by
  let A := A(k)
  let c := ComplexShape.up ℤ
  let E := boundedAboveProjectiveEquivalence k
  let Y := Cor.mk j.right
  let P := (projectivePairModel k).obj j
  let P₀ := projectiveRepresentableSingle k Y
  let h := projectiveAmbientLift k j
  let hi := (projectiveSingleRepresentativeIso k Y).hom
  let hj := E.unitIso.inv.app P
  let B := F.mapHomotopyCategory c
  let d := A.mapDerivedCategory
  let q : HomotopyCategory PST(k) c ⥤ DerivedCategory PST(k) := DerivedCategory.Qh
  let l : HomotopyCategory NST(k) c ⥤ DerivedCategory NST(k) := DerivedCategory.Qh
  let f := B.map h.hom
  let t := A.mapDerivedCategoryFactorsh
  let z := DerivedCategory.quotientCompQhIso NST(k)
  let g := ((F ⋙ A).mapHomologicalComplex c).map (ambientCochainMap k j)
  have hh : (E.inverse.map (projectivePairAmbientMap k j)).hom ≫ hj.hom = hi.hom ≫ h.hom :=
    congrArg (fun x => x.hom) (chosenProjectivePairAmbient k j)
  have hb : B.map ((E.inverse.map (projectivePairAmbientMap k j)).hom) ≫ B.map hj.hom =
      B.map hi.hom ≫ f := by rw [← B.map_comp, ← B.map_comp, hh]
  have ht : d.map (q.map f) ≫ t.hom.app (B.obj P.obj) =
      t.hom.app (B.obj P₀.obj) ≫ l.map ((A.mapHomotopyCategory c).map f) := t.hom.naturality f
  have hz : l.map ((A.mapHomotopyCategory c).map f) ≫ z.hom.app _ =
      z.hom.app _ ≫ (Qs(k)).map g := by
    change l.map ((HomotopyCategory.quotient _ c).map g) ≫ _ = _
    exact DerivedCategory.quotientCompQhIso_hom_naturality g
  change d.map (q.map (B.map ((E.inverse.map (projectivePairAmbientMap k j)).hom))) ≫
      (d.map (q.map (B.map hj.hom)) ≫ t.hom.app (B.obj P.obj) ≫ z.hom.app _) =
    (d.map (q.map (B.map hi.hom)) ≫ t.hom.app (B.obj P₀.obj) ≫ z.hom.app _) ≫
      (Qs(k)).map g
  rw [← Category.assoc, ← d.map_comp, ← q.map_comp, hb, q.map_comp, d.map_comp,
    Category.assoc, Category.assoc, Category.assoc, reassoc_of% ht, hz]
  rfl

/-- The unreduced projective Laurent tensor of the ambient single
is the original Laurent product in degree zero. -/
@[no_expose]
def projectiveAmbientLaurentIso (X : Sm(k)) :
    (projectiveTorusTensorToDerivedMinus k).obj (singleTransferRepresentable k (Cor.mk X)) ≅
      (S(k)).obj ((smoothTransferRepresentable k).obj (torusCylinder.obj X)) :=
  ObjectProperty.isoMk _ (projectiveTorusRepresentableSingleModelIso k (Cor.mk X) ≪≫
    Qs(k).mapIso (laurentCochainEndpointIso k X))

/-- The ambient Laurent comparison retains the actual projective single and
cochain endpoint maps. -/
theorem projectiveAmbientLaurentIso_hom_hom (X : Sm(k)) :
    (projectiveAmbientLaurentIso k X).hom.hom =
      (projectiveTorusRepresentableSingleModelIso k (Cor.mk X)).hom ≫
        Qs(k).map (laurentCochainEndpointIso k X).hom := by
  unfold projectiveAmbientLaurentIso
  exact Eq.refl _

/-- The actual ambient Laurent quotient, with the source and target of the
two original comparison isomorphisms fixed. -/
def projectiveAmbientLaurentQuotient {U X : Sm(k)} (j : U ⟶ X) :
    (S(k)).obj ((smoothTransferRepresentable k).obj (torusCylinder.obj X)) ⟶
      (S(k)).obj ((transferPairCokernelFunctor k).obj ((laurentPair k).obj (Arrow.mk j))) :=
  (S(k)).map (transferPairSequence k ((laurentPair k).obj (Arrow.mk j))).g

end AlgebraicGeometry.MotivicHomotopy
