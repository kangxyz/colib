/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.ProjectiveModel
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterTensor.RepresentableProjector
import Colib.Algebra.Homology.CochainComplex.SplitFactorization.ArrowMap

/-!
# The Laurent projector on the original relative cochain complex

Termwise Laurent product takes the graph of the original open inclusion
to its literal product graph. The Laurent projector on the mapping cone
is the map of cones induced by the structural projection and unit.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "Sm" => SmoothSite S
local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "a" => nisnevichSheafify k
local notation "F" => parameterTensorFunctor (SmoothSite.multiplicativeGroupObject S)
local notation "J" => (F ⋙ a)
local notation "c" => ComplexShape.up ℤ
local notation "s" => CochainComplex.singleFunctor NST 0
local notation "R" => representableLarge k
local notation "M" => smoothTransferRepresentable k
local notation "B" => @torusCylinder S
local notation "γ" => Cor.graphFunctor k

/-- The canonical abelian structure on sheaves with transfers. -/
local instance laurentCochainAbelian : Abelian NST := SheafWithTransfers.abelian k

/-- Apply the actual Laurent cylinder to the two objects and map of a pair. -/
abbrev laurentPair : Arrow Sm ⥤ Arrow Sm := (B).mapArrow

set_option maxHeartbeats 550000 in
-- The two coefficient maps are carried by literal graphs of the smooth-site section.
/-- The projector is induced by projection and the original Laurent unit at each end. -/
def laurentPairProjector (j : Arrow Sm) : (laurentPair k).obj j ⟶ (laurentPair k).obj j := by
  let G := SmoothSite.multiplicativeGroupObject S
  let z : B ⟶ B := projection G ≫ unitSection
  let f := (B).map j.hom
  exact (Arrow.homMk' (z.app j.left) (z.app j.right) (z.naturality j.hom).symm :
    Arrow.mk f ⟶ Arrow.mk f)

/-- The coefficient projector before applying the actual Nisnevich sheafification. -/
abbrev laurentTensorProjector : F ⟶ F :=
  torusParameterTensorProjection k ≫ torusParameterTensorUnit k

/-- Laurent product on the original degree zero graph representative. -/
def laurentCochainEndpointIso (X : Sm) :
    ((J).mapHomologicalComplex c).obj ((projectiveSmoothSingle k).obj X) ≅
      (s).obj ((M).obj ((B).obj X)) :=
  (HomologicalComplex.singleMapHomologicalComplex J c (0 : ℤ)).app ((R).obj (Cor.mk X)) ≪≫
    (s).mapIso ((a).mapIso (parameterTensorRepresentableIso
      (SmoothSite.multiplicativeGroupObject S) (Cor.mk X)))

set_option maxHeartbeats 500000 in
-- The graph of the literal Laurent product is expressed on its two representables.
/-- The Laurent endpoint comparison respects the original graph maps. -/
theorem laurentCochainEndpointIso_naturality {X Y : Sm} (f : X ⟶ Y) :
    ((J).mapHomologicalComplex c).map ((projectiveSmoothSingle k).map f) ≫
        (laurentCochainEndpointIso k Y).hom =
      (laurentCochainEndpointIso k X).hom ≫ (s).map ((M).map ((B).map f)) := by
  let G := SmoothSite.multiplicativeGroupObject S
  let e := HomologicalComplex.singleMapHomologicalComplex J c (0 : ℤ)
  let x := (R).obj (Cor.mk X)
  let y := (R).obj (Cor.mk Y)
  let r : x ⟶ y := (R).map ((γ).map f)
  let r' := (R).map ((γ).map ((B).map f))
  let t (V : Sm) := (parameterTensorRepresentableIso G (Cor.mk V)).hom
  have hn : (F).map r ≫ t Y = t X ≫ r' :=
    (parameterTensorRepresentableIso_hom_naturality G ((γ).map f)).trans
      (congrArg (fun q => t X ≫ (R).map q) (Cor.parameterProduct_graph G f))
  have ha : (J).map r ≫ (a).map (t Y) = (a).map (t X) ≫ (a).map r' :=
    ((a).map_comp _ _).symm.trans (((a).congr_map hn).trans ((a).map_comp _ _))
  have hs : (s).map ((J).map r) ≫ (s).map ((a).map (t Y)) =
      (s).map ((a).map (t X)) ≫ (s).map ((a).map r') :=
    ((s).map_comp _ _).symm.trans (((s).congr_map ha).trans ((s).map_comp _ _))
  let f₀ := ((J).mapHomologicalComplex c).map ((CochainComplex.singleFunctor PST 0).map r)
  let d₀ := e.hom.app x
  let d₁ := e.hom.app y
  let u₀ := (s).map ((a).map (t X))
  let u₁ := (s).map ((a).map (t Y))
  let g := (s).map ((a).map r')
  have he : f₀ ≫ d₁ = d₀ ≫ (s).map ((J).map r) := e.hom.naturality r
  change f₀ ≫ d₁ ≫ u₁ = (d₀ ≫ u₀) ≫ g
  calc
    _ = (f₀ ≫ d₁) ≫ u₁ := (Category.assoc _ _ _).symm
    _ = (d₀ ≫ (s).map ((J).map r)) ≫ u₁ := congrArg (· ≫ u₁) he
    _ = d₀ ≫ u₀ ≫ g := (Category.assoc _ _ _).trans (congrArg (d₀ ≫ ·) hs)
    _ = _ := (Category.assoc _ _ _).symm

private theorem laurentCochainEndpointIso_projector (X : Sm) :
    ((Functor.whiskerRight (laurentTensorProjector k) a).mapHomologicalComplex c).app
        ((projectiveSmoothSingle k).obj X) ≫ (laurentCochainEndpointIso k X).hom =
      (laurentCochainEndpointIso k X).hom ≫
        (s).map ((M).map ((projection (SmoothSite.multiplicativeGroupObject S)).app X ≫
          unitSection.app X)) := by
  let η := Functor.whiskerRight (laurentTensorProjector k) a
  let P := (R).obj (Cor.mk X)
  let G := SmoothSite.multiplicativeGroupObject S
  let t := (parameterTensorRepresentableIso G (Cor.mk X)).hom
  let e := (HomologicalComplex.singleMapHomologicalComplex J c (0 : ℤ)).app P
  let b := (R).map ((γ).map ((projection G).app X ≫ unitSection.app X))
  have h : (laurentTensorProjector k).app P ≫ t = t ≫ b :=
    (torusParameterTensorProjector_representable k (Cor.mk X)).trans
      (congrArg (fun q => t ≫ (R).map q) (torusUnitProjector_eq_graph k (Cor.mk X)))
  change (η.mapHomologicalComplex c).app ((CochainComplex.singleFunctor PST 0).obj P) ≫
      e.hom ≫ (s).map ((a).map t) =
    (e.hom ≫ (s).map ((a).map t)) ≫ (s).map ((a).map b)
  have hₐ : η.app P ≫ (a).map t = (a).map t ≫ (a).map b :=
    ((a).map_comp _ _).symm.trans (((a).congr_map h).trans ((a).map_comp _ _))
  have hₛ : (s).map (η.app P) ≫ (s).map ((a).map t) =
      (s).map ((a).map t) ≫ (s).map ((a).map b) :=
    ((s).map_comp _ _).symm.trans (((s).congr_map hₐ).trans ((s).map_comp _ _))
  have he : (η.mapHomologicalComplex c).app ((CochainComplex.singleFunctor PST 0).obj P) =
      e.hom ≫ (s).map (η.app P) ≫ e.inv :=
    HomologicalComplex.natTransMapHomologicalComplex_app_single_obj η c (0 : ℤ) P
  rw [he]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact congrArg (e.hom ≫ ·) hₛ

private abbrev laurentCochainTensor : CochainComplex PST ℤ ⥤ CochainComplex NST ℤ :=
  (J).mapHomologicalComplex c

private abbrev transferCochainCone :
    Arrow (CochainComplex NST ℤ) ⥤ CochainComplex NST ℤ :=
  CochainComplex.mappingConeNatTransFunctor (Arrow.leftToRight (C := CochainComplex NST ℤ))

private abbrev projectiveCochainArrow (b : Arrow Sm) : Arrow (CochainComplex PST ℤ) :=
  Arrow.mk ((projectivePairArrow k).app b)

private abbrev projectiveCochainArrowMap {i j : Arrow Sm} (φ : i ⟶ j) :
    projectiveCochainArrow k i ⟶ projectiveCochainArrow k j :=
  Arrow.homMk' ((projectiveSmoothSingle k).map φ.left)
    ((projectiveSmoothSingle k).map φ.right) ((projectivePairArrow k).naturality φ)

private abbrev laurentTransferCochainArrow (b : Arrow Sm) : Arrow (CochainComplex NST ℤ) :=
  Arrow.mk (cochainTransferPair k ((laurentPair k).obj b)).f

private abbrev laurentTransferCochainArrowMap {i j : Arrow Sm} (φ : i ⟶ j) :
    laurentTransferCochainArrow k i ⟶ laurentTransferCochainArrow k j :=
  ShortComplex.fFunctor.map
    ((s).mapShortComplex.map (transferPairSequenceMap k ((laurentPair k).map φ)))

private abbrev laurentConeComparison (b : Arrow Sm) :
    (laurentCochainTensor k).obj ((projectivePairCochain k).obj b) ≅
      (transferCochainCone k).obj
        ((laurentCochainTensor k).mapArrow.obj (projectiveCochainArrow k b)) :=
  CochainComplex.mappingCone.mapHomologicalComplexIso (projectiveCochainArrow k b).hom J

set_option maxHeartbeats 700000 in
-- Elaborate the two degree-zero endpoints and the corresponding arrow structures.
private def laurentCochainArrowIso (j : Arrow Sm) :
    (laurentCochainTensor k).mapArrow.obj (projectiveCochainArrow k j) ≅
      laurentTransferCochainArrow k j := by
  let g := ((J).mapHomologicalComplex c).map ((projectivePairArrow k).app j)
  let h := (cochainTransferPair k ((laurentPair k).obj j)).f
  let e₁ := laurentCochainEndpointIso k j.left
  let e₂ := laurentCochainEndpointIso k j.right
  have he : e₁.hom ≫ h = g ≫ e₂.hom :=
    (laurentCochainEndpointIso_naturality k j.hom).symm
  exact Arrow.isoMk (f := Arrow.mk g) (g := Arrow.mk h) e₁ e₂ he

/-- The comparison of literal termwise Laurent product with the literal
projective cone of the Laurent pair, followed by Nisnevich sheafification. -/
@[no_expose]
def laurentCochainComparison (j : Arrow Sm) :
    ((J).mapHomologicalComplex c).obj ((projectivePairCochain k).obj j) ≅
      cochainTransferPairCone k ((laurentPair k).obj j) := by
  exact laurentConeComparison k j ≪≫ (transferCochainCone k).mapIso (laurentCochainArrowIso k j)

set_option maxHeartbeats 650000 in
-- Compare the arrow components before applying the cone functor.
private theorem laurentCochainArrowIso_naturality {i j : Arrow Sm} (φ : i ⟶ j) :
    (laurentCochainTensor k).mapArrow.map (projectiveCochainArrowMap k φ) ≫
        (laurentCochainArrowIso k j).hom =
      (laurentCochainArrowIso k i).hom ≫ laurentTransferCochainArrowMap k φ := by
  apply Arrow.hom_ext
  · exact laurentCochainEndpointIso_naturality k φ.left
  · exact laurentCochainEndpointIso_naturality k φ.right

set_option maxHeartbeats 650000 in
-- Match the cone map of the original graph arrow with the generic cone comparison.
private theorem laurentConeComparison_naturality {i j : Arrow Sm} (φ : i ⟶ j) :
    (laurentCochainTensor k).map ((projectivePairCochain k).map φ) ≫
        (laurentConeComparison k j).hom =
      (laurentConeComparison k i).hom ≫ (transferCochainCone k).map
        ((laurentCochainTensor k).mapArrow.map (projectiveCochainArrowMap k φ)) := by
  let u := projectiveCochainArrowMap k φ
  let K := CochainComplex.mappingConeNatTransFunctor
    (Arrow.leftToRight (C := CochainComplex PST ℤ))
  have h : (projectivePairCochain k).map φ = K.map u := rfl
  exact (congrArg (fun x => (laurentCochainTensor k).map x ≫
    (laurentConeComparison k j).hom) h).trans
    (CochainComplex.SplitFactorization.coneMapIso_naturality_arrow J u)

set_option maxHeartbeats 600000 in
-- Expose the composition of the two concrete cone isomorphisms.
private theorem laurentCochainComparison_hom (b : Arrow Sm) :
    (laurentCochainComparison k b).hom =
      (laurentConeComparison k b).hom ≫
        (transferCochainCone k).map (laurentCochainArrowIso k b).hom := rfl

set_option maxHeartbeats 750000 in
-- Apply the cone functor after both original arrow squares have been identified.
private theorem laurentCochainComparison_naturality_aux {i j : Arrow Sm} (φ : i ⟶ j) :
    let f := (laurentCochainTensor k).map ((projectivePairCochain k).map φ)
    let C := transferCochainCone k
    let e (b : Arrow Sm) := (laurentCochainArrowIso k b).hom
    let m (b : Arrow Sm) := (laurentConeComparison k b).hom
    f ≫ (m j ≫ C.map (e j)) =
      (m i ≫ C.map (e i)) ≫ C.map (laurentTransferCochainArrowMap k φ) := by
  intro f C e m
  let u := (laurentCochainTensor k).mapArrow.map (projectiveCochainArrowMap k φ)
  let v := laurentTransferCochainArrowMap k φ
  exact CochainComplex.SplitFactorization.comp_map_of_commSq C u v (e i) (e j) f (m i) (m j)
    (laurentCochainArrowIso_naturality k φ) (laurentConeComparison_naturality k φ)

set_option maxHeartbeats 1200000 in
-- Use the comparison on the original projective maps and quotient maps of the two pairs.
/-- Termwise Laurent product takes a pair map to the original Laurent pair map. -/
theorem laurentCochainComparison_naturality {i j : Arrow Sm} (φ : i ⟶ j) :
    let m := ((J).mapHomologicalComplex c).map ((projectivePairCochain k).map φ)
    let q := cochainTransferPairConeMap k ((laurentPair k).map φ)
    m ≫ (laurentCochainComparison k j).hom = (laurentCochainComparison k i).hom ≫ q := by
  intro m q
  rw [laurentCochainComparison_hom k j, laurentCochainComparison_hom k i]
  exact laurentCochainComparison_naturality_aux k φ

/-- The literal augmentation of the Laurent cone to the Laurent transfer quotient. -/
abbrev laurentCochainAugmentation (j : Arrow Sm) :
    cochainTransferPairCone k ((laurentPair k).obj j) ⟶
      (s).obj ((transferPairCokernelFunctor k).obj ((laurentPair k).obj j)) :=
  CochainComplex.mappingCone.descShortComplex (cochainTransferPair k ((laurentPair k).obj j))

private theorem quasiIso_singleConeAugmentation {C : Type*} [Category* C] [Abelian C]
    {T : ShortComplex C} (hT : T.ShortExact) :
    QuasiIso (CochainComplex.mappingCone.descShortComplex
      (T.map (CochainComplex.singleFunctor C 0))) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex
    (hT.map_of_exact (CochainComplex.singleFunctor C 0))

set_option maxHeartbeats 650000 in
-- Apply the degree zero result to the literal short exact sequence of the open pair.
/-- The Laurent augmentation is a quasi-isomorphism for a Laurent open pair. -/
theorem quasiIso_laurentCochainAugmentation {U X : Sm} (j : U ⟶ X)
    [IsOpenImmersion ((B).map j).left] :
    QuasiIso (laurentCochainAugmentation k (Arrow.mk j)) := by
  let p : Arrow Sm := Arrow.mk ((B).map j)
  have h₀ : (transferPairSequence k p).ShortExact := transferPairSequence_shortExact k ((B).map j)
  exact quasiIso_singleConeAugmentation h₀

private abbrev laurentSheafifiedProjector : J ⟶ J :=
  Functor.whiskerRight (laurentTensorProjector k) a

private abbrev laurentCochainProjector : laurentCochainTensor k ⟶ laurentCochainTensor k :=
  (laurentSheafifiedProjector k).mapHomologicalComplex c

private abbrev laurentCochainProjectorSquare (j : Arrow Sm) :
    (laurentCochainTensor k).mapArrow.obj (projectiveCochainArrow k j) ⟶
      (laurentCochainTensor k).mapArrow.obj (projectiveCochainArrow k j) :=
  Arrow.homMk' ((laurentCochainProjector k).app ((projectiveSmoothSingle k).obj j.left))
    ((laurentCochainProjector k).app ((projectiveSmoothSingle k).obj j.right))
    ((laurentCochainProjector k).naturality (projectiveCochainArrow k j).hom).symm

private abbrev laurentTransferCochainProjector (j : Arrow Sm) :
    laurentTransferCochainArrow k j ⟶ laurentTransferCochainArrow k j :=
  ShortComplex.fFunctor.map
    ((s).mapShortComplex.map (transferPairSequenceMap k (laurentPairProjector k j)))

set_option maxHeartbeats 650000 in
-- Compare the two components of the actual projector on the arrows.
private theorem laurentCochainArrowIso_projector (j : Arrow Sm) :
    laurentCochainProjectorSquare k j ≫ (laurentCochainArrowIso k j).hom =
      (laurentCochainArrowIso k j).hom ≫ laurentTransferCochainProjector k j := by
  apply Arrow.hom_ext
  · exact laurentCochainEndpointIso_projector k j.left
  · exact laurentCochainEndpointIso_projector k j.right

set_option maxHeartbeats 650000 in
-- Evaluate the generic comparison at the actual coefficient projector.
private theorem laurentConeComparison_projector (j : Arrow Sm) :
    (laurentCochainProjector k).app ((projectivePairCochain k).obj j) ≫
        (laurentConeComparison k j).hom =
      (laurentConeComparison k j).hom ≫
        (transferCochainCone k).map (laurentCochainProjectorSquare k j) :=
  CochainComplex.SplitFactorization.coneMapIso_naturalTransformation_arrow J
    (laurentSheafifiedProjector k) (projectiveCochainArrow k j)

set_option maxHeartbeats 750000 in
-- Apply the original cone functor to the quotient projector square.
/-- The Laurent cochain comparison takes the projective coefficient projector
to the literal map on cones given by projection and unit. -/
theorem laurentCochainComparison_projector (j : Arrow Sm) :
    ((Functor.whiskerRight (laurentTensorProjector k) a).mapHomologicalComplex c).app
        ((projectivePairCochain k).obj j) ≫ (laurentCochainComparison k j).hom =
      (laurentCochainComparison k j).hom ≫
        cochainTransferPairConeMap k (laurentPairProjector k j) := by
  let f := (laurentCochainProjector k).app ((projectivePairCochain k).obj j)
  let p := laurentCochainProjectorSquare k j
  let q := laurentTransferCochainProjector k j
  let e := (laurentCochainArrowIso k j).hom
  let m := (laurentConeComparison k j).hom
  let C := transferCochainCone k
  have hn : f ≫ (m ≫ C.map e) = (m ≫ C.map e) ≫ C.map q :=
    CochainComplex.SplitFactorization.comp_map_of_commSq C p q e e f m m
      (laurentCochainArrowIso_projector k j) (laurentConeComparison_projector k j)
  calc
    _ = f ≫ (m ≫ C.map e) := congrArg (f ≫ ·) (laurentCochainComparison_hom k j)
    _ = (m ≫ C.map e) ≫ C.map q := hn
    _ = _ := congrArg (· ≫ cochainTransferPairConeMap k (laurentPairProjector k j))
      (laurentCochainComparison_hom k j).symm

/-- The augmentation carries the Laurent projector to the original map
of the quotient sheaf. -/
theorem laurentCochainComparison_projector_augmented (j : Arrow Sm) :
    ((Functor.whiskerRight (laurentTensorProjector k) a).mapHomologicalComplex c).app
        ((projectivePairCochain k).obj j) ≫
      (laurentCochainComparison k j).hom ≫ laurentCochainAugmentation k j =
    (laurentCochainComparison k j).hom ≫ laurentCochainAugmentation k j ≫
      (s).map ((transferPairCokernelFunctor k).map (laurentPairProjector k j)) := by
  rw [← Category.assoc, laurentCochainComparison_projector, Category.assoc]
  exact congrArg ((laurentCochainComparison k j).hom ≫ ·)
    (cochainTransferPairConeMap_desc k (laurentPairProjector k j))

end AlgebraicGeometry.MotivicHomotopy
