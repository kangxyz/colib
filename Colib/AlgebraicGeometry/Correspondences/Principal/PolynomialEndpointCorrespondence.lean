/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.RetainedSourceEndpointCycles
public import Colib.AlgebraicGeometry.Correspondences.Principal.BoundaryEndpointCycles

/-! # Actual original polynomial correspondence endpoints -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

/-- The original curve source-target map. -/
def retainedCurveMap {k : Type u} [Field k] {X C V Y : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (h : Y ⟶ Spec (.of k)) (q : C ⟶ X)
    (j : V ⟶ C) (g : V ⟶ Y) (hg : j ≫ q ≫ p = g ≫ h) : V ⟶ pullback p h :=
  pullback.lift (j ≫ q) g hg

/-- The unchanged retained polynomial source-target map is over the original base. -/
theorem polynomialRetained_over {k : Type u} [Field k] {X C V Y : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (h : Y ⟶ Spec (.of k)) (q : C ⟶ X)
    (j : V ⟶ C) (g : V ⟶ Y) (hg : j ≫ q ≫ p = g ≫ h) :
    lineMap (q ≫ p) j ≫ lineMap p q ≫ (projection p ≫ p) =
      (projection (j ≫ (q ≫ p)) ≫ g) ≫ h := by
  rw [lineMap_projection_assoc, lineMap_projection_assoc]
  simpa only [Category.assoc] using congrArg (fun a => projection (j ≫ (q ≫ p)) ≫ a) hg

variable {k : Type u} [Field k] {X C V W B Y : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsAffine X] [IsIntegral X] [Smooth p] [IsSeparated p]
    (h : Y ⟶ Spec (.of k)) [Smooth h] [IsSeparated h]
    (q : C ⟶ X) [IsProper q] [IsIntegral C] [IsNoetherian C]
    (j : V ⟶ C) [IsOpenImmersion j] [V.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (v : W ⟶ C) [IsOpenImmersion v]
    (b : B ⟶ W) [Nonempty B]
    (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ v))
    (f : Γ(W, ⊤)) (hf : b.appTop f = 1)
    [IsIntegral (parameterSpace (q ≫ p))] [IsNoetherian (parameterSpace (q ≫ p))]
    (g : V ⟶ Y) (hg : j ≫ q ≫ p = g ≫ h)
    [Nonempty (ambientUnitOpen (q ≫ p) v f)]

local instance : IsAffineHom (projection p) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback _ _).flip inferInstance

local instance : IsAffine (parameterSpace p) := isAffine_of_isAffineHom (projection p)

local instance : Smooth (projection p) := by
  have := PrincipalFamilyEndpointCuts.projection_smoothOfRelativeDimension p
  exact SmoothOfRelativeDimension.smooth 1 _

local instance : IsProper (lineMap p q) :=
  MorphismProperty.of_isPullback (lineMap_isPullback p q).flip inferInstance

local instance : IsAffineHom (projection (j ≫ (q ≫ p))) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback _ _).flip inferInstance

local instance : (parameterSpace (j ≫ (q ≫ p))).IsQuasiAffine :=
  Scheme.IsQuasiAffine.of_isAffineHom (projection (j ≫ (q ≫ p)))

local instance : SmoothOfRelativeDimension 1 (lineMap (q ≫ p) j ≫ lineMap p q) :=
  MorphismProperty.of_isPullback
    ((lineMap_isPullback (q ≫ p) j).paste_horiz (lineMap_isPullback p q)).flip inferInstance

omit [IsIntegral X] [IsSeparated p] [IsIntegral C] in
/-- The original outer graph map, including its residue degrees and coincident
images, is the pushforward of the unchanged retained whole source endpoint. -/
theorem componentEndpointCycle_eq_retainedPushforward
    (z : (principalCycle (parameterSpace (q ≫ p))
      (ambientRationalFunction (q ≫ p) v f)).support) (c : k) :
    letI := retainedCurve_isNoetherian j
    letI := sourceEndpoint_isNoetherian p q c (integralComponentAt z.val).subschemeι
    PrincipalBoundary.componentEndpointCycle p h (lineMap p q) (lineMap (q ≫ p) j)
      (ambientUnitOpen (q ≫ p) v f)
      (complement_subset_ambientUnitOpen (q ≫ p) j v b hcover f hf)
      (ambientUnitSection (q ≫ p) v f) (isUnit_ambientUnitSection (q ≫ p) v f)
      (projection (j ≫ (q ≫ p)) ≫ g) (polynomialRetained_over p h q j g hg) z c =
      (principalCycle (parameterSpace (q ≫ p)) (ambientRationalFunction (q ≫ p) v f)) z.val •
        noetherianCyclePushforward (retainedCurveMap p h q j g hg)
          (noetherianCyclePushforward (retainedSourceEndpointMap p q j v b hcover f hf c z)
            (AlgebraicCycle.fundamentalCycle _)) := by
  let := PrincipalBoundary.base_isNoetherian p
  let := retainedCurve_isNoetherian j
  let := isIntegral_integralComponentAt z.val
  let := sourceEndpoint_isNoetherian p q c (integralComponentAt z.val).subschemeι
  let U := ambientUnitOpen (q ≫ p) v f
  let hU := complement_subset_ambientUnitOpen (q ≫ p) j v b hcover f hf
  let F := ambientUnitSection (q ≫ p) v f
  let hF := isUnit_ambientUnitSection (q ≫ p) v f
  let gA := projection (j ≫ (q ≫ p)) ≫ g
  let hgA := polynomialRetained_over p h q j g hg
  let r := PrincipalBoundary.componentMap (projection p ≫ p) h (lineMap p q)
    (lineMap (q ≫ p) j) U hU F hF gA hgA z
  let w := PrincipalBoundary.imagePoint (projection p ≫ p) h (lineMap p q)
    (lineMap (q ≫ p) j) U hU F hF gA hgA z
  let e : (integralComponentAt z.val).subscheme ⟶ (integralComponentAt w).subscheme :=
    integralImageMap r
  let n := (integralComponentAt w).subschemeι ≫ pullback.fst (projection p ≫ p) h
  have hp : e ≫ n = (integralComponentAt z.val).subschemeι ≫ lineMap p q :=
    PrincipalBoundary.componentEndpoint_source_projection p h (lineMap p q)
      (lineMap (q ≫ p) j) U hU F hF gA hgA z
  let α := pullback.congrHom (rfl : endpoint p c = endpoint p c) hp
  let l := retainedSourceEndpointMap p q j v b hcover f hf c z
  let a := retainedCurveMap p h q j g hg
  let t := correspondenceGraphFiberMap p (projection p ≫ p) h w (endpoint p c) (by simp)
  have hn : IsFinite n :=
    (PrincipalBoundary.imagePoint_admissible (projection p ≫ p) h (lineMap p q)
      (lineMap (q ≫ p) j) U hU F hF gA hgA z).1
  have : IsFinite r := PrincipalBoundary.componentMap_isFinite (projection p ≫ p) h
    (lineMap p q) (lineMap (q ≫ p) j) U hU F hF gA hgA z
  have : IsFinite e := integralImageMap_isFinite r
  let := polynomialEndpoint_isNoetherian p (e ≫ n) c
  have hαfst : α.hom ≫ pullback.fst (endpoint p c)
      ((integralComponentAt z.val).subschemeι ≫ lineMap p q) =
      pullback.fst (endpoint p c) (e ≫ n) := by
    simp only [α, pullback.congrHom_hom, pullback.map, pullback.lift_fst, Category.comp_id]
  have hαsnd : α.hom ≫ pullback.snd (endpoint p c)
      ((integralComponentAt z.val).subschemeι ≫ lineMap p q) =
      pullback.snd (endpoint p c) (e ≫ n) := by
    simp only [α, pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id]
  let R : (integralComponentAt z.val).subscheme ⟶ parameterSpace (j ≫ (q ≫ p)) :=
    PrincipalBoundary.retainedMap (lineMap (q ≫ p) j) U hU F hF z
  have hl : l = pullback.snd (endpoint p c)
      ((integralComponentAt z.val).subschemeι ≫ lineMap p q) ≫
        R ≫ projection (j ≫ (q ≫ p)) := rfl
  have hlj : l ≫ j = sourceEndpointToCurve p q c (integralComponentAt z.val).subschemeι :=
    retainedSourceEndpointMap_inclusion p q j v b hcover f hf c z
  have hi : e ≫ (integralComponentAt w).subschemeι = r := integralImageMap_inclusion r
  have hrs : r ≫ pullback.snd (projection p ≫ p) h = R ≫ gA := pullback.lift_snd _ _ _
  have haf : a ≫ pullback.fst p h = j ≫ q := pullback.lift_fst _ _ _
  have has : a ≫ pullback.snd p h = g := pullback.lift_snd _ _ _
  have htf : t ≫ pullback.fst p h = pullback.fst (endpoint p c) n :=
    correspondenceGraphFiberMap_fst p (projection p ≫ p) h w (endpoint p c) (by simp)
  have hts : t ≫ pullback.snd p h = pullback.snd (endpoint p c) n ≫
      (integralComponentAt w).subschemeι ≫ pullback.snd (projection p ≫ p) h :=
    correspondenceGraphFiberMap_snd p (projection p ≫ p) h w (endpoint p c) (by simp)
  have hmap : α.hom ≫ (l ≫ a) = polynomialEndpointMap p n e c ≫ t := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [haf, htf, polynomialEndpointMap_fst, ← Category.assoc l, hlj,
        sourceEndpointToCurve_base, hαfst]
    · simp only [Category.assoc]
      rw [has, hts, hl]
      simp only [Category.assoc]
      rw [← Category.assoc α.hom, hαsnd]
      rw [← Category.assoc (polynomialEndpointMap p n e c), polynomialEndpointMap_snd]
      simp only [Category.assoc]
      have HO : e ≫ ((integralComponentAt w).subschemeι ≫
          pullback.snd (projection p ≫ p) h) = R ≫ gA :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (fun a => a ≫ pullback.snd (projection p ≫ p) h) hi).trans hrs)
      simpa only [Category.assoc, gA] using congrArg
        (fun a => pullback.snd (endpoint p c) (e ≫ n) ≫ a) HO.symm
  have H := finiteCyclePushforward_fundamentalCycle_iso α
  rw [← noetherianCyclePushforward_eq_finiteCyclePushforward] at H
  have HT := congrArg (noetherianCyclePushforward (l ≫ a)) H
  rw [noetherianCyclePushforward_comp_apply, hmap] at HT
  have ht : IsFinite t := isFinite_correspondenceGraphFiberMap p (projection p ≫ p) h w
    (endpoint p c) (by simp)
    (PrincipalBoundary.imagePoint_admissible (projection p ≫ p) h (lineMap p q)
      (lineMap (q ≫ p) j) U hU F hF gA hgA z)
  rw [noetherianCyclePushforward_eq_finiteCyclePushforward] at HT
  change (principalCycle (parameterSpace (q ≫ p))
    (ambientRationalFunction (q ≫ p) v f)) z.val •
      finiteCyclePushforward (polynomialEndpointMap p n e c ≫ t)
        (AlgebraicCycle.fundamentalCycle _) = _
  rw [noetherianCyclePushforward_comp_apply]
  exact congrArg (fun Z => (principalCycle (parameterSpace (q ≫ p))
    (ambientRationalFunction (q ≫ p) v f)) z.val • Z) HT

omit [IsIntegral C] [Nonempty (ambientUnitOpen (q ≫ p) v f)] in
/-- The actual original polynomial correspondence paired with its original scalar
endpoint graph is the unchanged outer map of the whole retained source cycle. -/
theorem polynomialCorrespondence_endpointGraph_val (c : k) :
    let hX : (genericPoints X).Finite := by
      rw [genericPoints_eq_singleton]
      exact Set.finite_singleton _
    letI := retainedCurve_isNoetherian j
    (incidenceTorPairing p (projection p ≫ p) h
      (graphCorrespondenceOfComponents p (projection p ≫ p) (endpoint p c) (by simp) hX)
      (PrincipalPolynomialFamily.correspondence p h q j v b hcover f hf g hg)).val =
        noetherianCyclePushforward (retainedCurveMap p h q j g hg)
          (retainedSignedSourceEndpointCycle p q j v b hcover f hf c) := by
  classical
  let := retainedCurve_isNoetherian j
  let := nonempty_ambientUnitOpen_of_boundary (q ≫ p) v b f hf
  let Z := principalCycle (parameterSpace (q ≫ p)) (ambientRationalFunction (q ≫ p) v f)
  let := Z.finite_support.fintype
  dsimp only
  change (incidenceTorPairing p (projection p ≫ p) h _
    (PrincipalBoundary.correspondence (projection p ≫ p) h (lineMap p q)
      (lineMap (q ≫ p) j) (ambientUnitOpen (q ≫ p) v f)
      (complement_subset_ambientUnitOpen (q ≫ p) j v b hcover f hf)
      (ambientUnitSection (q ≫ p) v f) (isUnit_ambientUnitSection (q ≫ p) v f)
      (projection (j ≫ (q ≫ p)) ≫ g) (polynomialRetained_over p h q j g hg))).val = _
  rw [PrincipalBoundary.correspondence_endpointGraph_eq_sourceEndpointCycles]
  unfold retainedSignedSourceEndpointCycle
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  let := sourceEndpoint_isNoetherian p q c (integralComponentAt z.val).subschemeι
  have H := componentEndpointCycle_eq_retainedPushforward p h q j v b hcover f hf g hg z c
  exact H.trans (map_zsmul (noetherianCyclePushforward (retainedCurveMap p h q j g hg))
    _ _).symm

local instance {A D : Scheme.{u}} (i : A ⟶ D) [IsOpenImmersion i]
    [IsIntegral A] [IsIntegral D] : IsDominant i :=
  ⟨i.isOpenEmbedding.isOpen_range.dense ⟨i (genericPoint A), Set.mem_range_self _⟩⟩

variable [IsIntegral V] [IsIntegral W]

omit [Nonempty (ambientUnitOpen (q ≫ p) v f)] in
/-- The original polynomial correspondence has literal zero endpoint and original
principal-divisor endpoint. This is native finite-correspondence/AlgebraicCycle
equality with the unchanged retained outer map, not rational equivalence. -/
@[colib_tag "COL-1100", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/Chow/RationalEquivalence/FlatPullbackPrincipalDiviso\
    r.lean:585-627"
  "ingredient" "Original local fraction and order as full quotient-length difference; the \
    support and endpoint assembly is proved here."]
theorem polynomialCorrespondence_endpointGraph_zero_one :
    let hX : (genericPoints X).Finite := by
      rw [genericPoints_eq_singleton]
      exact Set.finite_singleton _
    letI := retainedCurve_isNoetherian j
    let G := fun c : k => graphCorrespondenceOfComponents p (projection p ≫ p)
      (endpoint p c) (by simp) hX
    let K := PrincipalPolynomialFamily.correspondence p h q j v b hcover f hf g hg
    incidenceTorPairing p (projection p ≫ p) h (G 0) K = 0 ∧
      (incidenceTorPairing p (projection p ≫ p) h (G 1) K).val =
        noetherianCyclePushforward (retainedCurveMap p h q j g hg)
          (principalCycle V (j.functionFieldMap (curveRationalFunction v f))) := by
  let := retainedCurve_isNoetherian j
  obtain ⟨H0, H1⟩ := retainedSignedSourceEndpointCycle_zero_one p q j v b hcover f hf
  dsimp only
  constructor
  · apply Subtype.ext
    change (incidenceTorPairing p (projection p ≫ p) h _ _).val = 0
    rw [polynomialCorrespondence_endpointGraph_val p h q j v b hcover f hf g hg 0,
      H0, map_zero]
  · rw [polynomialCorrespondence_endpointGraph_val p h q j v b hcover f hf g hg 1, H1]

omit [Nonempty (ambientUnitOpen (q ≫ p) v f)] in
/-- An already constructed native principal correspondence with the original
cycle has exactly the one endpoint of the original polynomial correspondence. -/
theorem polynomialCorrespondence_endpointGraph_eq_of_val
    (L : finiteCorrespondences p h)
    (hL : letI := retainedCurve_isNoetherian j
      L.val = noetherianCyclePushforward (retainedCurveMap p h q j g hg)
        (principalCycle V (j.functionFieldMap (curveRationalFunction v f)))) :
    let hX : (genericPoints X).Finite := by
      rw [genericPoints_eq_singleton]
      exact Set.finite_singleton _
    incidenceTorPairing p (projection p ≫ p) h
      (graphCorrespondenceOfComponents p (projection p ≫ p) (endpoint p 1) (by simp) hX)
      (PrincipalPolynomialFamily.correspondence p h q j v b hcover f hf g hg) = L := by
  apply Subtype.ext
  exact (polynomialCorrespondence_endpointGraph_zero_one p h q j v b hcover f hf g hg).2.trans
    hL.symm

end AlgebraicGeometry.PrincipalFamilyUnitOpen
