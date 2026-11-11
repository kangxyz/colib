/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholeFibers
public import Colib.AlgebraicGeometry.Scheme.ForgetBaseProduct

/-!
# Closed supports for the actual retained-product pencil

The relative-curve producer uses `D = X ×[S] V`, with the literal first and second
projections as source and target. This is a strictly more specific construction than
arbitrary maps `p : D ⟶ X` and `g : D ⟶ V`. The latter do not in general give a closed
embedding into the product over the ground ring.

Here the full polynomial parameter space of `D` is identified with
`(X × A¹) ×[S] V`. The existing `forgetBaseProductMap` then embeds it as a closed
subscheme of `(X × A¹) × V` when `S` is separated over the ground ring. The native
whole zero scheme is a closed subscheme of that ambient space, so its actual paired
map is closed. No finite pushforward degree is discarded for a general finite span.

The exact original specialization is in
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Data/Core.lean` and
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Common/CurveGeometry.lean`,
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PolynomialSectionPencil

variable {R : Type u} [CommRing R]

/-- The actual polynomial parameter map is a base change of the original source map. -/
theorem parameterMap_isPullback {D X : Scheme.{u}} (b : X ⟶ Spec (.of R)) (p : D ⟶ X) :
    IsPullback (projection (p ≫ b)) (parameterMap b p) p (projection b) where
  w := (parameterMap_projection b p).symm
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s ↦ by
    let l : s.pt ⟶ parameterSpace (p ≫ b) :=
      pullback.lift s.fst
        (s.snd ≫ pullback.snd b (Spec.map (CommRingCat.ofHom Polynomial.C))) (by
          rw [← Category.assoc, s.condition]
          simp only [Category.assoc, projection, pullback.condition])
    have hl : l ≫ projection (p ≫ b) = s.fst := pullback.lift_fst _ _ _
    have hr : l ≫ parameterMap b p = s.snd := by
      apply pullback.hom_ext
      · change _ ≫ projection b = _ ≫ projection b
        rw [Category.assoc, parameterMap_projection, ← Category.assoc, hl]
        exact s.condition
      · simp [l, parameterMap]
    refine ⟨l, hl, hr, ?_⟩
    intro m hm hn
    apply pullback.hom_ext
    · exact hm.trans hl.symm
    · have hs := congrArg (fun z ↦ z ≫
          pullback.snd b (Spec.map (CommRingCat.ofHom Polynomial.C))) hn
      simpa only [Category.assoc, parameterMap_snd, l, pullback.lift_snd] using hs)⟩

variable {S X V : Scheme.{u}} (t : S ⟶ Spec (.of R)) (q : X ⟶ S) (r : V ⟶ S)

/-- The polynomial family of the unchanged retained product is itself a product
over the original base. Both projections are literal maps, with no support replacement. -/
def retainedParameterIso :
    parameterSpace (pullback.fst q r ≫ (q ≫ t)) ≅
      pullback (projection (q ≫ t) ≫ q) r :=
  ((parameterMap_isPullback (q ≫ t) (pullback.fst q r)).paste_horiz
    (IsPullback.of_hasPullback q r).flip).flip.isoPullback

@[reassoc (attr := simp)]
theorem retainedParameterIso_hom_fst :
    (retainedParameterIso t q r).hom ≫ pullback.fst (projection (q ≫ t) ≫ q) r =
      parameterMap (q ≫ t) (pullback.fst q r) := IsPullback.isoPullback_hom_fst _

@[reassoc (attr := simp)]
theorem retainedParameterIso_hom_snd :
    (retainedParameterIso t q r).hom ≫ pullback.snd (projection (q ≫ t) ≫ q) r =
      projection (pullback.fst q r ≫ (q ≫ t)) ≫ pullback.snd q r :=
  IsPullback.isoPullback_hom_snd _

/-- The full retained ambient scheme embedded into the source-cylinder/target product. -/
def retainedAmbientPair :
    parameterSpace (pullback.fst q r ≫ (q ≫ t)) ⟶
      pullback (projection (q ≫ t) ≫ (q ≫ t)) (r ≫ t) :=
  (retainedParameterIso t q r).hom ≫
    Scheme.forgetBaseProductMap t (projection (q ≫ t) ≫ q) r ≫
      (pullback.congrHom (Category.assoc (projection (q ≫ t)) q t) rfl).hom

@[reassoc (attr := simp)]
theorem retainedAmbientPair_fst :
    retainedAmbientPair t q r ≫ pullback.fst (projection (q ≫ t) ≫ (q ≫ t)) (r ≫ t) =
      parameterMap (q ≫ t) (pullback.fst q r) := by
  simp [retainedAmbientPair, pullback.congrHom_hom, pullback.map]

@[reassoc (attr := simp)]
theorem retainedAmbientPair_snd :
    retainedAmbientPair t q r ≫ pullback.snd (projection (q ≫ t) ≫ (q ≫ t)) (r ≫ t) =
      projection (pullback.fst q r ≫ (q ≫ t)) ≫ pullback.snd q r := by
  simp [retainedAmbientPair, pullback.congrHom_hom, pullback.map]

instance [IsSeparated t] : IsClosedImmersion (retainedAmbientPair t q r) := by
  unfold retainedAmbientPair
  infer_instance

variable (L : (pullback q r).Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property L] (a c : Γ(L, ⊤))

/-- The actual target leg of the full polynomial zero scheme, through the unchanged
retained product's second projection. -/
def retainedFamilyTarget :
    (familyZero (pullback.fst q r ≫ (q ≫ t)) L a c).subscheme ⟶ V :=
  (familyZero (pullback.fst q r ≫ (q ≫ t)) L a c).subschemeι ≫
    projection (pullback.fst q r ≫ (q ≫ t)) ≫ pullback.snd q r

/-- The actual paired support map of the whole polynomial zero scheme. -/
def retainedFamilyPair :
    (familyZero (pullback.fst q r ≫ (q ≫ t)) L a c).subscheme ⟶
      pullback (projection (q ≫ t) ≫ (q ≫ t)) (r ≫ t) :=
  (familyZero (pullback.fst q r ≫ (q ≫ t)) L a c).subschemeι ≫ retainedAmbientPair t q r

@[reassoc (attr := simp)]
theorem retainedFamilyPair_fst :
    retainedFamilyPair t q r L a c ≫
        pullback.fst (projection (q ≫ t) ≫ (q ≫ t)) (r ≫ t) =
      familySource (q ≫ t) (pullback.fst q r) L a c := by
  simp [retainedFamilyPair, familySource]

@[reassoc (attr := simp)]
theorem retainedFamilyPair_snd :
    retainedFamilyPair t q r L a c ≫
        pullback.snd (projection (q ≫ t) ≫ (q ≫ t)) (r ≫ t) =
      retainedFamilyTarget t q r L a c := by
  simp [retainedFamilyPair, retainedFamilyTarget]

instance [IsSeparated t] : IsClosedImmersion (retainedFamilyPair t q r L a c) := by
  unfold retainedFamilyPair
  infer_instance

/-- The two literal legs satisfy the required equation over the ground ring. -/
theorem retainedFamily_base :
    familySource (q ≫ t) (pullback.fst q r) L a c ≫ (projection (q ≫ t) ≫ (q ≫ t)) =
      retainedFamilyTarget t q r L a c ≫ (r ≫ t) := by
  rw [← retainedFamilyPair_fst, ← retainedFamilyPair_snd]
  simp only [Category.assoc, pullback.condition]

/-- The closed support is exactly the pullback lift of the literal source and target legs. -/
theorem retainedFamilyPair_eq_lift :
    retainedFamilyPair t q r L a c =
      pullback.lift (familySource (q ≫ t) (pullback.fst q r) L a c)
        (retainedFamilyTarget t q r L a c) (retainedFamily_base t q r L a c) := by
  apply pullback.hom_ext <;> simp

section ChangeParameter

variable {W : Scheme.{u}} (e : W ≅ parameterSpace (q ≫ t)) (w : W ⟶ Spec (.of R))
  (he : e.hom ≫ (projection (q ≫ t) ≫ (q ≫ t)) = w)

/-- Changing only the source parameter by its actual scheme isomorphism gives
an isomorphism of the two source/target products. -/
def retainedProductParameterIso :
    pullback (projection (q ≫ t) ≫ (q ≫ t)) (r ≫ t) ≅ pullback w (r ≫ t) :=
  asIso (pullback.map _ _ _ _ e.inv (𝟙 V) (𝟙 (Spec (.of R)))
    (by rw [← he]; simp) (by simp))

@[reassoc (attr := simp)]
theorem retainedProductParameterIso_hom_fst :
    (retainedProductParameterIso t q r e w he).hom ≫ pullback.fst w (r ≫ t) =
      pullback.fst (projection (q ≫ t) ≫ (q ≫ t)) (r ≫ t) ≫ e.inv := by
  simp [retainedProductParameterIso, pullback.map]

@[reassoc (attr := simp)]
theorem retainedProductParameterIso_hom_snd :
    (retainedProductParameterIso t q r e w he).hom ≫ pullback.snd w (r ≫ t) =
      pullback.snd (projection (q ≫ t) ≫ (q ≫ t)) (r ≫ t) := by
  simp [retainedProductParameterIso, pullback.map]

/-- The same whole closed support with the source parameter transported by an
actual isomorphism. This transport changes neither the zero scheme nor its target. -/
def retainedFamilyPairWithParameter :
    (familyZero (pullback.fst q r ≫ (q ≫ t)) L a c).subscheme ⟶ pullback w (r ≫ t) :=
  retainedFamilyPair t q r L a c ≫ (retainedProductParameterIso t q r e w he).hom

@[reassoc (attr := simp)]
theorem retainedFamilyPairWithParameter_fst :
    retainedFamilyPairWithParameter t q r L a c e w he ≫ pullback.fst w (r ≫ t) =
      familySource (q ≫ t) (pullback.fst q r) L a c ≫ e.inv := by
  simp [retainedFamilyPairWithParameter]

@[reassoc (attr := simp)]
theorem retainedFamilyPairWithParameter_snd :
    retainedFamilyPairWithParameter t q r L a c e w he ≫ pullback.snd w (r ≫ t) =
      retainedFamilyTarget t q r L a c := by
  simp [retainedFamilyPairWithParameter]

instance [IsSeparated t] :
    IsClosedImmersion (retainedFamilyPairWithParameter t q r L a c e w he) := by
  unfold retainedFamilyPairWithParameter
  infer_instance

end ChangeParameter

/-- The existing native additive-cylinder comparison is over the actual ground scheme. -/
@[reassoc]
theorem nativeParameterIso_hom_base (A : CommRingCat.{u}) (U : SmoothSite (Spec A)) :
    (nativeParameterIso A U).hom ≫ (projection U.hom ≫ U.hom) =
      (SmoothSite.Contraction.affineLineCylinder.obj U).hom :=
  (SmoothSite.Contraction.affineCylinderPolynomialIso A U).hom.w

section NativeParameter

variable [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)]

/-- The literal retained polynomial support, now paired with the active native
additive cylinder rather than a replacement parameter object. -/
def nativeRetainedFamilyPair :
    (familyZero (pullback.fst q r ≫ (q ≫ t)) L a c).subscheme ⟶
      pullback (SmoothSite.Contraction.affineLineCylinder.obj (SmoothSite.mk (q ≫ t))).hom
        (r ≫ t) :=
  retainedFamilyPairWithParameter t q r L a c
    (nativeParameterIso (.of R) (SmoothSite.mk (q ≫ t))) _
    (nativeParameterIso_hom_base (.of R) (SmoothSite.mk (q ≫ t)))

@[reassoc (attr := simp)]
theorem nativeRetainedFamilyPair_fst :
    nativeRetainedFamilyPair t q r L a c ≫ pullback.fst _ _ =
      familySource (q ≫ t) (pullback.fst q r) L a c ≫
        (nativeParameterIso (.of R) (SmoothSite.mk (q ≫ t))).inv := by
  simp [nativeRetainedFamilyPair]

@[reassoc (attr := simp)]
theorem nativeRetainedFamilyPair_snd :
    nativeRetainedFamilyPair t q r L a c ≫ pullback.snd _ _ =
      retainedFamilyTarget t q r L a c := by
  simp [nativeRetainedFamilyPair]

instance [IsSeparated t] : IsClosedImmersion (nativeRetainedFamilyPair t q r L a c) := by
  unfold nativeRetainedFamilyPair
  infer_instance

end NativeParameter

end AlgebraicGeometry.Scheme.PolynomialSectionPencil
