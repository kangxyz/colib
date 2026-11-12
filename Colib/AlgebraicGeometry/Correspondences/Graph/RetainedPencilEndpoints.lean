/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedPencilCartesianEndpoint
public import Colib.AlgebraicGeometry.Correspondences.Spans.FiniteFlat.RelativeSupportIsomorphism

/-!
# Genuine zero and one endpoints of the retained-product polynomial family

The producer is exactly the retained product, not arbitrary source and target
maps. Its actual paired map is closed by the existing separated-base theorem.
The whole finite-flat hypothesis is transported through the actual cylinder
isomorphism. Graph precomposition then gives the full literal zero schemes of
the two original sections, with the actual source and target projections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Divisors Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.PolynomialSectionPencil
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction

private theorem cartesianEndpointSpan_eq_of_iso {A B C D E S : Scheme.{u}} [IsNoetherian A]
    (a : A ⟶ S) (c : C ⟶ S) [IsSeparated c] [LocallyOfFiniteType c]
    (σ : A ⟶ B) (f : D ⟶ B) (g : D ⟶ C) (hFin : IsFinite f) (hFlat : Flat f)
    (h : pullback.fst σ f ≫ a = (pullback.snd σ f ≫ g) ≫ c)
    (e : pullback σ f ≅ E)
    (p : E ⟶ A) (hpFin : IsFinite p) (hpFlat : Flat p) (q : E ⟶ C)
    (h' : p ≫ a = q ≫ c)
    (hp : e.hom ≫ p = pullback.fst σ f) (hq : e.hom ≫ q = pullback.snd σ f ≫ g) :
    cartesianEndpointSpan a c σ f g hFin hFlat h =
      ofFiniteFlatSpanRaw a c p (hFin := hpFin) (hFlat := hpFlat) q h' := by
  let : IsFinite f := hFin
  let : Flat f := hFlat
  let : IsFinite p := hpFin
  let : Flat p := hpFlat
  exact ofFiniteFlatSpanRaw_eq_of_iso a c e (pullback.fst σ f) (pullback.snd σ f ≫ g) h
    p q h' hp hq

/-- The original paired family and the two projection comparisons for its entire section fiber. -/
structure NativeSectionEndpointData {k : Type u} [Field k]
    (U W : SmoothSite (Spec (.of k))) (s : k) (D E : Scheme.{u}) where
  /-- The whole family source leg on the native cylinder. -/
  source : D ⟶ (affineLineCylinder.obj U).left
  /-- The whole family target leg. -/
  target : D ⟶ W.left
  sourceFinite : IsFinite source
  sourceFlat : Flat source
  familyOverBase : source ≫ (affineLineCylinder.obj U).hom = target ≫ W.hom
  pairClosed : IsClosedImmersion (pullback.lift source target familyOverBase)
  cartesianOverBase : pullback.fst (nativeAffineSection (.of k) U s).left source ≫ U.hom =
    (pullback.snd (nativeAffineSection (.of k) U s).left source ≫ target) ≫ W.hom
  /-- The isomorphism from the entire Cartesian fiber to the original support. -/
  fiberIso : pullback (nativeAffineSection (.of k) U s).left source ≅ E
  /-- The source leg on `E`, identified with the first projection of the section fiber. -/
  fiberSource : E ⟶ U.left
  fiberSourceFinite : IsFinite fiberSource
  fiberSourceFlat : Flat fiberSource
  /-- The target leg on `E`, obtained from the family target on the section fiber. -/
  fiberTarget : E ⟶ W.left
  fiberOverBase : fiberSource ≫ U.hom = fiberTarget ≫ W.hom
  fiberSource_eq : fiberIso.hom ≫ fiberSource =
    pullback.fst (nativeAffineSection (.of k) U s).left source
  fiberTarget_eq : fiberIso.hom ≫ fiberTarget =
    pullback.snd (nativeAffineSection (.of k) U s).left source ≫ target

/-- The full section span agrees with any support isomorphism preserving both actual legs. -/
theorem nativeSection_comp_span_legs_of_iso {k : Type u} [Field k] {D E : Scheme.{u}}
    (U W : SmoothSite (Spec (.of k))) (s : k)
    (d : NativeSectionEndpointData (k := k) U W s D E) :
    letI : IsNoetherian ((𝟭 Scheme).obj (affineLineCylinder.obj U).left) :=
      SmoothSite.isNoetherian_left (affineLineCylinder.obj U)
    letI : IsNoetherian ((𝟭 Scheme).obj U.left) := SmoothSite.isNoetherian_left U
    NativeSectionSpanSpecialization (k := k) U W s
      (ofFiniteFlatSpanRaw (affineLineCylinder.obj U).hom W.hom d.source
        (hFin := d.sourceFinite) (hFlat := d.sourceFlat) d.target d.familyOverBase)
      (ofFiniteFlatSpanRaw U.hom W.hom d.fiberSource
        (hFin := d.fiberSourceFinite) (hFlat := d.fiberSourceFlat)
        d.fiberTarget d.fiberOverBase) := by
  let : IsNoetherian ((𝟭 Scheme).obj U.left) := inferInstanceAs (IsNoetherian U.left)
  let m := pullback.lift d.source d.target d.familyOverBase
  let : IsClosedImmersion m := d.pairClosed
  have hSpec := nativeSection_comp_span_legs (k := k) U W s m
    d.source d.target d.sourceFinite d.sourceFlat
    (pullback.lift_fst d.source d.target d.familyOverBase)
    (pullback.lift_snd d.source d.target d.familyOverBase) d.familyOverBase d.cartesianOverBase
  exact NativeSectionSpanSpecialization.congr_right (k := k) hSpec
    (cartesianEndpointSpan_eq_of_iso U.hom W.hom (nativeAffineSection (.of k) U s).left
      d.source d.target d.sourceFinite d.sourceFlat d.cartesianOverBase d.fiberIso
      d.fiberSource d.fiberSourceFinite d.fiberSourceFlat d.fiberTarget
      d.fiberOverBase d.fiberSource_eq d.fiberTarget_eq)

variable {k : Type u} [Field k] {S X V : Scheme.{u}}
  (t : S ⟶ Spec (.of k)) (q : X ⟶ S) (r : V ⟶ S)
  [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)]
  (L : (pullback q r).Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property L] (a c : Γ(L, ⊤))

local notation "U" => SmoothSite.mk (q ≫ t)
local notation "W" => SmoothSite.mk (r ≫ t)
local notation "F" => nativeRetainedFamilySource (k := k) t q r L a c
local notation "G" => retainedFamilyTarget (R := k) t q r L a c

/-- The actual native family map is the closed lift of the two specified legs. -/
theorem nativeRetainedFamilyLift_isClosedImmersion [IsSeparated t] :
    IsClosedImmersion (pullback.lift F G (nativeRetainedFamily_base (k := k) t q r L a c)) := by
  rw [← nativeRetainedFamilyPair_eq_lift (k := k) t q r L a c]
  infer_instance

variable [Smooth (r ≫ t)] [IsSeparated (r ≫ t)] [QuasiCompact (r ≫ t)]

/-- The zero-endpoint proof on the exact raw span data. -/
@[no_expose]
abbrev nativeRetainedFamilyZeroProof [IsSeparated t]
    (hFamilyFin : IsFinite F) (hFamilyFlat : Flat F) :=
  let u : SmoothSite (Spec (.of k)) := U
  let v : SmoothSite (Spec (.of k)) := W
  let D := (familyZero (pullback.fst q r ≫ (q ≫ t)) L a c).subscheme
  let f : D ⟶ (affineLineCylinder.obj u).left := F
  let g : D ⟶ v.left := G
  let Z := (zeroScheme (pullback q r) L a).subscheme
  let p : Z ⟶ u.left := (zeroScheme (pullback q r) L a).subschemeι ≫ pullback.fst q r
  let w : Z ⟶ v.left := (zeroScheme (pullback q r) L a).subschemeι ≫ pullback.snd q r
  let σ := (nativeAffineSection (.of k) u 0).left
  let e : pullback σ f ≅ Z := nativeZeroFiberIso (k := k) u (pullback.fst q r) L a c
  let hFam : f ≫ (affineLineCylinder.obj u).hom = g ≫ v.hom :=
    nativeRetainedFamily_base (k := k) t q r L a c
  let hm : IsClosedImmersion (pullback.lift f g hFam) :=
    nativeRetainedFamilyLift_isClosedImmersion (k := k) t q r L a c
  let h := nativeRetainedZero_finite_flat (k := k) t q r L a c
    (_hFamilyFin := hFamilyFin) (_hFamilyFlat := hFamilyFlat)
  let d : NativeSectionEndpointData (k := k) u v 0 D Z := {
    source := f
    target := g
    sourceFinite := hFamilyFin
    sourceFlat := hFamilyFlat
    familyOverBase := hFam
    pairClosed := hm
    cartesianOverBase := nativeRetainedEndpoint_base (k := k) t q r L a c 0
    fiberIso := e
    fiberSource := p
    fiberSourceFinite := h.1
    fiberSourceFlat := h.2
    fiberTarget := w
    fiberOverBase := retainedZero_base (k := k) t q r L a
    fiberSource_eq := nativeZeroFiberIso_hom_base (k := k) u (pullback.fst q r) L a c
    fiberTarget_eq := nativeZeroFiberIso_hom_original_assoc (k := k) u (pullback.fst q r) L a c
      (pullback.snd q r) }
  nativeSection_comp_span_legs_of_iso (k := k) u v 0 d

/-- Literal zero specialization, retaining the whole original zero scheme and both legs. -/
theorem nativeRetainedFamily_zero [IsSeparated t]
    (hFamilyFin : IsFinite F) (hFamilyFlat : Flat F) :
    type_of% (nativeRetainedFamilyZeroProof (k := k) t q r L a c hFamilyFin hFamilyFlat) :=
  nativeRetainedFamilyZeroProof (k := k) t q r L a c hFamilyFin hFamilyFlat

/-- The one-endpoint proof on the exact raw span data. -/
@[no_expose]
abbrev nativeRetainedFamilyOneProof [IsSeparated t]
    (hFamilyFin : IsFinite F) (hFamilyFlat : Flat F) :=
  let u : SmoothSite (Spec (.of k)) := U
  let v : SmoothSite (Spec (.of k)) := W
  let D := (familyZero (pullback.fst q r ≫ (q ≫ t)) L a c).subscheme
  let f : D ⟶ (affineLineCylinder.obj u).left := F
  let g : D ⟶ v.left := G
  let Z := (zeroScheme (pullback q r) L c).subscheme
  let p : Z ⟶ u.left := (zeroScheme (pullback q r) L c).subschemeι ≫ pullback.fst q r
  let w : Z ⟶ v.left := (zeroScheme (pullback q r) L c).subschemeι ≫ pullback.snd q r
  let σ := (nativeAffineSection (.of k) u 1).left
  let e : pullback σ f ≅ Z := nativeOneFiberIso (k := k) u (pullback.fst q r) L a c
  let hFam : f ≫ (affineLineCylinder.obj u).hom = g ≫ v.hom :=
    nativeRetainedFamily_base (k := k) t q r L a c
  let hm : IsClosedImmersion (pullback.lift f g hFam) :=
    nativeRetainedFamilyLift_isClosedImmersion (k := k) t q r L a c
  let h := nativeRetainedOne_finite_flat (k := k) t q r L a c
    (_hFamilyFin := hFamilyFin) (_hFamilyFlat := hFamilyFlat)
  let d : NativeSectionEndpointData (k := k) u v 1 D Z := {
    source := f
    target := g
    sourceFinite := hFamilyFin
    sourceFlat := hFamilyFlat
    familyOverBase := hFam
    pairClosed := hm
    cartesianOverBase := nativeRetainedEndpoint_base (k := k) t q r L a c 1
    fiberIso := e
    fiberSource := p
    fiberSourceFinite := h.1
    fiberSourceFlat := h.2
    fiberTarget := w
    fiberOverBase := retainedZero_base (k := k) t q r L c
    fiberSource_eq := nativeOneFiberIso_hom_base (k := k) u (pullback.fst q r) L a c
    fiberTarget_eq := nativeOneFiberIso_hom_original_assoc (k := k) u (pullback.fst q r) L a c
      (pullback.snd q r) }
  nativeSection_comp_span_legs_of_iso (k := k) u v 1 d

/-- Literal one specialization, retaining the whole original zero scheme and both legs. -/
theorem nativeRetainedFamily_one [IsSeparated t]
    (hFamilyFin : IsFinite F) (hFamilyFlat : Flat F) :
    type_of% (nativeRetainedFamilyOneProof (k := k) t q r L a c hFamilyFin hFamilyFlat) :=
  nativeRetainedFamilyOneProof (k := k) t q r L a c hFamilyFin hFamilyFlat

end AlgebraicGeometry.Cor
