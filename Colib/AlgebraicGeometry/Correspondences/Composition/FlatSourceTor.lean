/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.OriginalKoszulPointTransport
public import Colib.AlgebraicGeometry.Correspondences.Composition.PairTorZero
public import Colib.AlgebraicGeometry.Intersection.SmoothDiagonalGraphList

/-!
# Actual incidence Tor when the second support is flat over its source

The support product maps flatly to the graph product of the first support's
actual target projection. The common smooth diagonal list is regular on that
actual graph product for an arbitrary target projection. Flat pullback then
makes its identical image regular on the entire support-product stalk.
The existing original support Koszul comparison kills positive native Tor.
Neither the first support nor its target projection is assumed flat.

The source of the graph-product parameter is locally Noetherian, as required
by the accepted common-list theorem. Smooth finite correspondences over a field
satisfy this condition. Degree zero is the existing full incidence stalk, not
its reduction. This packet is source only; no elaboration is claimed.

Adapted from motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
Graph/Flat/LeftComposition.lean:38-195. The actual native supports, stalks,
Koszul comparison and Tor modules replace the original generator wrapper.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- The graph ambient of the first actual support's target projection. -/
abbrev correspondenceSupportGraphProduct : Scheme.{u} :=
  pullback (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g) g

/-- The coefficient-to-graph map keeps the first support and uses the second source. -/
def correspondenceSupportProductToGraph :
    correspondenceSupportProduct f g h z w ⟶ correspondenceSupportGraphProduct f g z :=
  pullback.map _ _ _ _ (𝟙 _) ((integralComponentAt w).subschemeι ≫ pullback.fst g h)
    (𝟙 S) (by simp) (by simp)

/-- Flatness is supplied by the second support projection, not by the parameter map. -/
instance correspondenceSupportProductToGraph_flat
    [Flat ((integralComponentAt w).subschemeι ≫ pullback.fst g h)] :
    Flat (correspondenceSupportProductToGraph f g h z w) :=
  MorphismProperty.pullbackMap (P := @Flat) (inferInstanceAs (Flat (𝟙 _)))
    (inferInstanceAs (Flat ((integralComponentAt w).subschemeι ≫ pullback.fst g h)))
    (by simp) (by simp)

/-- The graph product remembers the same two middle coordinates as the ambient. -/
def correspondenceSupportGraphMiddle :
    correspondenceSupportGraphProduct f g z ⟶ pullback g g :=
  pullback.map _ _ g g ((integralComponentAt z).subschemeι ≫ pullback.snd f g)
    (𝟙 Y) (𝟙 S) (by simp) (by simp)

/-- The two actual maps from the support product to the middle self-product agree. -/
@[reassoc] theorem correspondenceSupportProduct_graphMiddle :
    correspondenceSupportProductToGraph f g h z w ≫ correspondenceSupportGraphMiddle f g z =
      correspondenceSupportProductInclusion f g h z w ≫ correspondenceMiddlePair f g h := by
  apply pullback.hom_ext <;>
    simp [correspondenceSupportProductToGraph, correspondenceSupportGraphMiddle,
      correspondenceSupportProductInclusion, correspondenceMiddlePair, pullback.map]

/-- At an actual incidence point the graph-product middle coordinates are diagonal. -/
theorem correspondenceSupportGraphMiddle_incidence
    (x : correspondenceIncidence f g h z w) :
    correspondenceSupportGraphMiddle f g z
        (correspondenceSupportProductToGraph f g h z w
          (correspondenceIncidenceToSupportProduct f g h z w x)) =
      pullback.diagonal g
        (correspondenceTripleMiddle f g h (correspondenceIncidenceInclusion f g h z w x)) := by
  have he : correspondenceIncidenceToSupportProduct f g h z w ≫
      correspondenceSupportProductToGraph f g h z w ≫
        correspondenceSupportGraphMiddle f g z =
      correspondenceIncidenceInclusion f g h z w ≫
        correspondenceTripleMiddle f g h ≫ pullback.diagonal g := by
    rw [correspondenceSupportProduct_graphMiddle,
      ← Category.assoc, ← correspondenceIncidence_ambient_comm]
    simpa only [Category.assoc] using congrArg
      (fun m => correspondenceIncidenceInclusion f g h z w ≫ m)
      (correspondenceTriple_isPullback f g h).w.symm
  exact congrArg (fun m => m x) he

/-- The point used by the graph list is the literal original middle point. -/
theorem correspondenceSupportGraphMiddle_point_eq
    (x : correspondenceIncidence f g h z w) :
    correspondenceSupportGraphMiddle f g z
        (correspondenceSupportProductToGraph f g h z w
          (correspondenceIncidenceToSupportProduct f g h z w x)) =
      correspondenceMiddlePair f g h (correspondenceIncidenceAmbientInclusion f g h z w x) := by
  change _ = correspondenceMiddlePair f g h
    (correspondenceTripleInclusion f g h (correspondenceIncidenceInclusion f g h z w x))
  rw [correspondenceIncidence_ambient_point_eq]
  exact congrArg (fun m => m (correspondenceIncidenceToSupportProduct f g h z w x))
    (correspondenceSupportProduct_graphMiddle f g h z w)

/-- The full diagonal ideal is preserved by the actual point transport. -/
private theorem diagonal_ker_transport [IsSeparated g] (y : Y) (q : pullback (C := Scheme) g g)
    (hq : q = pullback.diagonal g y) :
    RingHom.ker (((pullback g g).presheaf.stalkCongr (.of_eq hq)).hom ≫
      (pullback.diagonal g).stalkMap y).hom =
        IdealSheafData.stalk (pullback.diagonal g).ker q := by
  subst q
  simpa [TopCat.Presheaf.stalkCongr] using
    ker_stalkMap_eq_idealStalk_ker (pullback.diagonal g) y

/-- The two paths of actual stalk maps agree, including both equality transports. -/
theorem correspondenceSupportGraph_stalkMap_comp
    (x : correspondenceIncidence f g h z w) :
    let d := correspondenceIncidenceToSupportProduct f g h z w x
    let p := correspondenceIncidenceAmbientInclusion f g h z w x
    let η := correspondenceSupportProductToGraph f g h z w
    let γ := correspondenceSupportGraphMiddle f g z
    let e := (pullback g g).presheaf.stalkCongr
      (.of_eq (correspondenceSupportGraphMiddle_point_eq f g h z w x))
    e.hom ≫ (correspondenceMiddlePair f g h).stalkMap p ≫
        ((correspondenceIntersectionAmbient f g h).presheaf.stalkCongr
          (.of_eq (correspondenceIncidence_ambient_point_eq f g h z w x))).hom ≫
        (correspondenceSupportProductInclusion f g h z w).stalkMap d =
      γ.stalkMap (η d) ≫ η.stalkMap d := by
  let d := correspondenceIncidenceToSupportProduct f g h z w x
  let η := correspondenceSupportProductToGraph f g h z w
  let γ := correspondenceSupportGraphMiddle f g z
  let i := correspondenceSupportProductInclusion f g h z w
  let m := correspondenceMiddlePair f g h
  have aux (p : correspondenceIntersectionAmbient f g h) (hp : p = i d)
      (hy : γ (η d) = m p) :
      ((pullback g g).presheaf.stalkCongr (.of_eq hy)).hom ≫ m.stalkMap p ≫
        ((correspondenceIntersectionAmbient f g h).presheaf.stalkCongr
          (.of_eq hp)).hom ≫ i.stalkMap d = γ.stalkMap (η d) ≫ η.stalkMap d := by
    subst p
    simpa only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
      Category.id_comp, Category.assoc, Scheme.Hom.stalkMap_comp] using
      (Scheme.Hom.stalkMap_congr_hom (η ≫ γ) (i ≫ m)
        (correspondenceSupportProduct_graphMiddle f g h z w) d).symm
  exact aux _ (correspondenceIncidence_ambient_point_eq f g h z w x)
    (correspondenceSupportGraphMiddle_point_eq f g h z w x)

/-- A common actual middle list is regular on the entire support-product stalk. -/
theorem correspondenceIncidence_flatSource_regularList
    [Smooth g] [IsSeparated g] [IsLocallyNoetherian (integralComponentAt z).subscheme]
    [Flat ((integralComponentAt w).subschemeι ≫ pullback.fst g h)]
    (x : correspondenceIncidence f g h z w) :
    let d := correspondenceIncidenceToSupportProduct f g h z w x
    let η := correspondenceSupportProductToGraph f g h z w
    let γ := correspondenceSupportGraphMiddle f g z
    ∃ (r : ℕ) (t : Fin r → (pullback g g).presheaf.stalk (γ (η d))),
      IsRegular ((pullback g g).presheaf.stalk (γ (η d))) (List.ofFn t) ∧
      Ideal.ofList (List.ofFn t) = IdealSheafData.stalk (pullback.diagonal g).ker (γ (η d)) ∧
      IsRegular ((correspondenceSupportProduct f g h z w).presheaf.stalk d)
        (List.ofFn (fun j => (η.stalkMap d).hom ((γ.stalkMap (η d)).hom (t j)))) := by
  let d := correspondenceIncidenceToSupportProduct f g h z w x
  let η := correspondenceSupportProductToGraph f g h z w
  let γ := correspondenceSupportGraphMiddle f g z
  obtain ⟨r, t, ht, hk, hG⟩ :=
    Scheme.Hom.exists_isRegular_diagonalStalkList_graphPair g
      ((integralComponentAt z).subschemeι ≫ pullback.snd f g) (η d)
      (correspondenceTripleMiddle f g h (correspondenceIncidenceInclusion f g h z w x))
      (correspondenceSupportGraphMiddle_incidence f g h z w x)
  refine ⟨r, t, ht, ?_, ?_⟩
  · rw [Ideal.ofList_ofFn]
    exact hk.trans (diagonal_ker_transport g _ _
      (correspondenceSupportGraphMiddle_incidence f g h z w x))
  · let A := (correspondenceSupportGraphProduct f g z).presheaf.stalk (η d)
    let B := (correspondenceSupportProduct f g h z w).presheaf.stalk d
    let : Algebra A B := (η.stalkMap d).hom.toAlgebra
    have : Module.Flat A B := Flat.stalkMap η d
    have : IsLocalHom (algebraMap A B) := inferInstanceAs (IsLocalHom (η.stalkMap d).hom)
    have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
    change IsRegular A (List.ofFn (fun j => (γ.stalkMap (η d)).hom (t j))) at hG
    have H := hG.of_faithfullyFlat (R := A) (S := B)
    change IsRegular B ((List.ofFn (fun j => (γ.stalkMap (η d)).hom (t j))).map
      (η.stalkMap d).hom) at H
    simpa only [List.map_ofFn, Function.comp_def] using H

/-- The genuine original ambient Tor has no positive degrees for a flat second source. -/
theorem isZero_correspondenceIncidenceTor_succ_of_flat_source
    [Flat f] [Smooth g] [IsSeparated g] [Flat h]
    [IsLocallyNoetherian (integralComponentAt z).subscheme]
    [Flat ((integralComponentAt w).subschemeι ≫ pullback.fst g h)]
    (x : correspondenceIncidence f g h z w) (n : ℕ) :
    IsZero (correspondenceIncidenceAmbientTor f g h z w x (n + 1)) := by
  let d := correspondenceIncidenceToSupportProduct f g h z w x
  let η := correspondenceSupportProductToGraph f g h z w
  let γ := correspondenceSupportGraphMiddle f g z
  obtain ⟨r, t, ht, hk, hD⟩ := correspondenceIncidence_flatSource_regularList f g h z w x
  let eU := (pullback g g).presheaf.stalkCongr
    (.of_eq (correspondenceSupportGraphMiddle_point_eq f g h z w x))
  let φ := correspondenceIncidenceSupportStalkMap f g h z w x
  let β := ((correspondenceMiddlePair f g h).stalkMap
    (correspondenceIncidenceAmbientInclusion f g h z w x)).hom
  have hmap (a : (pullback g g).presheaf.stalk (γ (η d))) :
      φ (β (eU.hom.hom a)) = (η.stalkMap d).hom ((γ.stalkMap (η d)).hom a) :=
    ConcreteCategory.congr_hom (correspondenceSupportGraph_stalkMap_comp f g h z w x) a
  let t' := fun j => eU.hom.hom ((List.ofFn t).get j)
  obtain ⟨ht', hk'⟩ := correspondenceOriginalMiddleList_stalkCongr f g h z w x
    (γ (η d)) (correspondenceSupportGraphMiddle_point_eq f g h z w x)
    (List.ofFn t) ht hk
  have hreg : IsRegular ((correspondenceSupportProduct f g h z w).presheaf.stalk d)
      (List.ofFn (fun j => φ (β (t' j)))) := by
    change IsRegular _ (List.ofFn
      ((fun a => φ (β (eU.hom.hom a))) ∘ (List.ofFn t).get))
    rw [← List.map_ofFn, List.ofFn_get, List.map_ofFn]
    simpa only [Function.comp_def, hmap] using hD
  have hzero := (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular
    (M := (correspondenceSupportProduct f g h z w).presheaf.stalk d)).2.1 hreg
      (n + 1) (Nat.succ_ne_zero n)
  let e := correspondenceIncidenceTorIsoOriginalSupportKoszul f g h z w x
    t' ht' hk' (n + 1)
  exact ((ModuleCat.restrictScalars φ).map_isZero hzero).of_iso e

end Stacks.Chow
