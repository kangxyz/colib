/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Gersten.PointPurity.Neighborhood
public import Colib.AlgebraicGeometry.MotivicHomotopy.Gysin.Coefficients.EffectiveSupport
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Cohomology.Absolute
import Colib.AlgebraicGeometry.MotivicHomotopy.Gysin.OpenNaturality

/-! # Compatible cohomology comparisons on smooth subneighborhoods -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme Opposite
open AlgebraicGeometry.Scheme.SmoothSite AlgebraicGeometry.MotivicHomotopy
open Stacks.Cohomology.FreeYonedaUnivLE

universe u w w' w''

namespace AlgebraicGeometry.SheafWithTransfers.Gersten

variable {k : Type u} [Field k]

local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))
local notation "K" => effectiveHICoefficient k
local notation "M" => effectiveSmoothMotive k

attribute [local irreducible] Cor.graphFunctor transferRepresentable

variable {X : SmoothSite (Spec (CommRingCat.of k))} {x : X.left}
  {U₀ : PointSupportNeighborhoods k X x}
  (h₀ : Smooth ((pointClosureInclusion k X x ∣_ U₀.1) ≫
    (Scheme.Opens.ι (X := X.left) U₀.1 ≫ X.hom)))

local notation "I" => Set.Iic U₀
local notation "i(" U ")" => smoothPointClosureInclusion (smoothPointClosureOn h₀ U)

private theorem relativeDimension_of_openImmersion
    {Y Z : SmoothSite (Spec (CommRingCat.of k))} (f : Y ⟶ Z)
    [IsOpenImmersion f.left] {d : ℕ} (h : RelativeDimension Z.hom d) :
    RelativeDimension Y.hom d :=
  relativeDimension_transport (MorphismProperty.Over.w f)
    (RelativeDimension.comp_isOpenImmersion f.left Z.hom h)

variable {a b : ℕ}
  (hX : RelativeDimension ((opensFunctor X).obj U₀.1).hom a)
  (hZ : RelativeDimension (smoothPointClosure h₀).hom b)

include hX in
private theorem relativeDimension_ambient (U : I) :
    RelativeDimension ((opensFunctor X).obj U.1.1).hom a := by
  let f := (opensFunctor X).map (homOfLE (show U.1.1 ≤ U₀.1 from U.2))
  let : IsOpenImmersion f.left := inferInstanceAs (IsOpenImmersion (X.left.homOfLE U.2))
  exact relativeDimension_of_openImmersion f hX

include hZ in
private theorem relativeDimension_center (U : I) :
    RelativeDimension ((smoothPointCenterFunctor h₀).obj U).hom b :=
  relativeDimension_of_openImmersion (smoothPointCenterInclusion h₀ U) hZ

private def subneighborhoodSupportIso (U : I) :
    pointSupportPair k X x U.1 ≅ Arrow.mk (closedPairOpenInclusion (i(U)).left) :=
  pointSupportPairIso k X x U.1 (i(U)).left (range_smoothPointClosureInclusion h₀ U)

private theorem subneighborhoodSupportIso_hom_right (U : I) :
    (subneighborhoodSupportIso h₀ U).hom.right = 𝟙 ((opensFunctor X).obj U.1.1) :=
  rfl

private theorem subneighborhoodSupportIso_naturality {U V : I} (r : U ⟶ V) :
    (pointSupportPairFunctor k X x).map (homOfLE (show U.1 ≤ V.1 from r.le)) ≫
        (subneighborhoodSupportIso h₀ V).hom =
      (subneighborhoodSupportIso h₀ U).hom ≫
        closedSupportArrowMap (smoothPointClosureMap_isPullback
          (smoothPointClosureOn h₀ U) (smoothPointClosureOn h₀ V) r.le) := by
  let t := (pointSupportPairFunctor k X x).map (homOfLE (show U.1 ≤ V.1 from r.le))
  let f := (opensFunctor X).map (homOfLE (show U.1.1 ≤ V.1.1 from r.le))
  let s := closedSupportArrowMap (smoothPointClosureMap_isPullback
    (smoothPointClosureOn h₀ U) (smoothPointClosureOn h₀ V) r.le)
  let eU := subneighborhoodSupportIso h₀ U
  let eV := subneighborhoodSupportIso h₀ V
  have ht : t.right = f := rfl
  have hs : s.right = f := rfl
  have hU : eU.hom.right = 𝟙 ((opensFunctor X).obj U.1.1) :=
    subneighborhoodSupportIso_hom_right h₀ U
  have hV : eV.hom.right = 𝟙 ((opensFunctor X).obj V.1.1) :=
    subneighborhoodSupportIso_hom_right h₀ V
  apply openPairArrowMap_eq_of_right
  change t.right ≫ eV.hom.right = eU.hom.right ≫ s.right
  exact (congrArg₂ (· ≫ ·) ht hV).trans
    ((Category.comp_id f).trans ((Category.id_comp f).symm.trans (congrArg₂ (· ≫ ·) hU hs).symm))


variable [PerfectField k]

attribute [local instance] effectiveSupportCoefficientCorSheafify
  effectiveSupportCoefficientSmoothSheafify

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (F : LargeSheaves k) (hF : F.obj.IsA1Invariant)

local notation "P" n => pointSupportSubneighborhoodInclusion k X x U₀ ⋙
  pointSupportCohomologyDiagram k X (K F hF) n x
local notation "C" => iteratedHIContraction k (a - b) F hF

private def subneighborhoodSupportedHomEquiv (U : I) (n : ℤ) :
    ((P n).obj (op U)) ≃+ (effectiveMotiveWithSupport k (i(U)) ⟶ (K F hF)⟦n⟧) :=
  let pairMotive : Arrow Sm ⥤ EffectiveMotivesMinus.{u, w'} k :=
    effectivePairMotiveFunctor.{u, w, w'} k
  let e := pairMotive.mapIso (subneighborhoodSupportIso h₀ U)
  AddEquiv.mk' e.homFromEquiv (fun a b => Preadditive.comp_add _ _ _ e.inv a b)

set_option maxHeartbeats 1000000 in
-- Compare the signed degree with negative cohomology on the centre.
include h₀ hX hZ in
/-- The supported cohomology of a smooth subneighborhood vanishes below the codimension. -/
theorem subneighborhoodSupport_eq_zero_of_lt (U : I) (n : ℤ)
    (hn : n < (a - b : ℕ)) (z : (P n).obj (op U)) : z = 0 := by
  let e := (subneighborhoodSupportedHomEquiv h₀ F hF U n).trans
    (effectiveSupportCohomologyEquiv k (i(U)) (relativeDimension_ambient hX U)
      (relativeDimension_center h₀ hZ U) F hF n)
  have hz : e z = 0 :=
    effectiveSmoothCohomology_eq_zero_of_neg k ((smoothPointCenterFunctor h₀).obj U)
      (C).1 (C).2 (n - ((a - b : ℕ) : ℤ)) (by omega) (e z)
  exact e.injective (hz.trans e.toAddMonoidHom.map_zero'.symm)

private def contractedDegreeIso (n : ℕ) (hn : a - b ≤ n) :
    (K (C).1 (C).2)⟦(n : ℤ) - ((a - b : ℕ) : ℤ)⟧ ≅
      (K (C).1 (C).2)⟦((n - (a - b) : ℕ) : ℤ)⟧ :=
  eqToIso (congrArg (fun r : ℤ => (K (C).1 (C).2)⟦r⟧) (Int.ofNat_sub hn).symm)

set_option maxHeartbeats 1000000 in
-- Use the effective comparison before evaluating ordinary cohomology on the smooth centre.
include hX hZ in
/-- The supported classes at a smooth subneighborhood are the ordinary
cohomology of its reduced closure with contracted coefficients. -/
@[no_expose]
def subneighborhoodSupportCohomologyEquiv (U : I) (n : ℕ) (hn : a - b ≤ n) :
    ((P(n : ℤ)).obj (op U)) ≃+
      ((smoothPointCenterFunctor h₀).op ⋙
        cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj (C).1) (n - (a - b))).obj (op U) :=
  let e := effectiveSupportCohomologyEquiv k (i(U)) (relativeDimension_ambient hX U)
    (relativeDimension_center h₀ hZ U) F hF (n : ℤ)
  let d := contractedDegreeIso F hF n hn
  (subneighborhoodSupportedHomEquiv h₀ F hF U (n : ℤ)).trans (e.trans
    ((AddEquiv.mk' d.homToEquiv (fun a b => Preadditive.add_comp _ _ _ a b d.hom)).trans
      (effectiveSmoothCohomologyEquiv k ((smoothPointCenterFunctor h₀).obj U)
        (C).1 (C).2 (n - (a - b)))))

set_option maxHeartbeats 1500000 in
-- Paste the complement comparison with the actual open restriction square of purity.
/-- The stagewise comparison induces the original restriction on cohomology of the centre. -/
theorem subneighborhoodSupportCohomologyEquiv_naturality {U V : I} (r : U ⟶ V)
    (n : ℕ) (hn : a - b ≤ n) (z : (P(n : ℤ)).obj (op V)) :
    subneighborhoodSupportCohomologyEquiv h₀ hX hZ F hF U n hn ((P(n : ℤ)).map r.op z) =
      (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj (C).1) (n - (a - b))).map
        ((smoothPointCenterFunctor h₀).map r).op
        (subneighborhoodSupportCohomologyEquiv h₀ hX hZ F hF V n hn z) := by
  let pairMotive : Arrow Sm ⥤ EffectiveMotivesMinus.{u, w'} k :=
    effectivePairMotiveFunctor.{u, w, w'} k
  let e := subneighborhoodSupportIso h₀ U
  let e' := subneighborhoodSupportIso h₀ V
  let t := (pointSupportPairFunctor k X x).map (homOfLE (show U.1 ≤ V.1 from r.le))
  let g := (smoothPointCenterFunctor h₀).map r
  let f := (opensFunctor X).map (homOfLE (show U.1.1 ≤ V.1.1 from r.le))
  let hi : IsPullback (i(U)).left g.left f.left (i(V)).left :=
    smoothPointClosureMap_isPullback (smoothPointClosureOn h₀ U) (smoothPointClosureOn h₀ V) r.le
  let s := closedSupportArrowMap hi
  have hc : t ≫ e'.hom = e.hom ≫ s := subneighborhoodSupportIso_naturality h₀ r
  have hci : e.inv ≫ t = s ≫ e'.inv := by
    apply (cancel_mono e'.hom).1
    have hl : (e.inv ≫ t) ≫ e'.hom = s :=
      (Category.assoc _ _ _).trans ((congrArg (e.inv ≫ ·) hc).trans (e.inv_hom_id_assoc s))
    have hr : (s ≫ e'.inv) ≫ e'.hom = s :=
      (Category.assoc _ _ _).trans ((congrArg (s ≫ ·) e'.inv_hom_id).trans (Category.comp_id s))
    exact hl.trans hr.symm
  have hm : pairMotive.map e.inv ≫ pairMotive.map t = pairMotive.map s ≫ pairMotive.map e'.inv :=
    (pairMotive.map_comp _ _).symm.trans
      ((pairMotive.congr_map hci).trans (pairMotive.map_comp _ _))
  have hv :
      subneighborhoodSupportedHomEquiv h₀ F hF U (n : ℤ) ((P(n : ℤ)).map r.op z) =
        pairMotive.map s ≫ subneighborhoodSupportedHomEquiv h₀ F hF V (n : ℤ) z := by
    change pairMotive.map e.inv ≫ pairMotive.map t ≫ z =
      pairMotive.map s ≫ pairMotive.map e'.inv ≫ z
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ z) hm).trans (Category.assoc _ _ _))
  let hXU := relativeDimension_ambient hX U
  let hZU := relativeDimension_center h₀ hZ U
  let hXV := relativeDimension_ambient hX V
  let hZV := relativeDimension_center h₀ hZ V
  let eU := effectiveSupportCohomologyEquiv k (i(U)) hXU hZU F hF (n : ℤ)
  let eV := effectiveSupportCohomologyEquiv k (i(V)) hXV hZV F hF (n : ℤ)
  let zV := subneighborhoodSupportedHomEquiv h₀ F hF V (n : ℤ) z
  let : IsOpenImmersion f.left := inferInstanceAs (IsOpenImmersion (X.left.homOfLE r.le))
  have he : eU (subneighborhoodSupportedHomEquiv h₀ F hF U (n : ℤ)
      ((P(n : ℤ)).map r.op z)) = (M).map g ≫ eV zV :=
    (congrArg eU hv).trans
      (effectiveSupportCohomologyEquiv_precomp k (i(U)) hXU hZU (i(V)) hXV hZV hi
        (effectivePurity_naturality_of_isOpenImmersion k hi hXU hZU hXV hZV) F hF (n : ℤ) zV)
  let d := contractedDegreeIso F hF n hn
  let C₀ := (C).1
  let hC₀ := (C).2
  let m := n - (a - b)
  let τU := effectiveSmoothCohomologyEquiv k ((smoothPointCenterFunctor h₀).obj U) C₀ hC₀ m
  let τV := effectiveSmoothCohomologyEquiv k ((smoothPointCenterFunctor h₀).obj V) C₀ hC₀ m
  let res := (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj C₀) m).map g.op
  change τU (eU (subneighborhoodSupportedHomEquiv h₀ F hF U (n : ℤ)
    ((P(n : ℤ)).map r.op z)) ≫ d.hom) = res (τV (eV zV ≫ d.hom))
  exact (congrArg (fun t => τU (t ≫ d.hom)) he).trans
    ((congrArg τU (Category.assoc _ _ _)).trans
      (effectiveSmoothCohomologyEquiv_precomp k g C₀ hC₀ m (eV zV ≫ d.hom)))

end AlgebraicGeometry.SheafWithTransfers.Gersten
