/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.PolynomialSections

/-!
# Whole polynomial fibers over the original source

These Cartesian comparisons preserve both original maps of the whole zero scheme.
No reduction, generic-point restriction, or flatness of integral components is used.
The base and total-space maps are adapted from
`Motivic/Aglib/AlgebraicGeometry/Modules/Invertible/Pencils/PolynomialBoundaryPencil.lean`,
blob `255fab996ba506779802f3f921fb40d88c258ebc`, at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial

open Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.PolynomialSectionPencil

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (b : X ⟶ Spec (.of R))

/-- The literal polynomial parameter change induced by a map of original bases. -/
def parameterMap {D : Scheme.{u}} (f : D ⟶ X) :
    parameterSpace (f ≫ b) ⟶ parameterSpace b :=
  pullback.lift (projection (f ≫ b) ≫ f)
    (pullback.snd (f ≫ b) (Spec.map (CommRingCat.ofHom Polynomial.C))) (by
      simpa only [projection, Category.assoc] using
        (pullback.condition (f := f ≫ b)
          (g := Spec.map (CommRingCat.ofHom Polynomial.C))))

@[reassoc (attr := simp)] theorem parameterMap_projection {D : Scheme.{u}} (f : D ⟶ X) :
    parameterMap b f ≫ projection b = projection (f ≫ b) ≫ f := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem parameterMap_snd {D : Scheme.{u}} (f : D ⟶ X) :
    parameterMap b f ≫ pullback.snd b (Spec.map (CommRingCat.ofHom Polynomial.C)) =
      pullback.snd (f ≫ b) (Spec.map (CommRingCat.ofHom Polynomial.C)) := pullback.lift_snd _ _ _

@[reassoc (attr := simp)] theorem endpoint_snd (c : R) :
    endpoint b c ≫ pullback.snd b (Spec.map (CommRingCat.ofHom Polynomial.C)) =
      b ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom c)) := pullback.lift_snd _ _ _

@[reassoc] theorem endpoint_parameterMap {D : Scheme.{u}} (f : D ⟶ X) (c : R) :
    endpoint (f ≫ b) c ≫ parameterMap b f = f ≫ endpoint b c := by
  apply pullback.hom_ext
  · change _ ≫ projection b = _ ≫ projection b
    simp
  · simp

/-- The endpoint square of the actual polynomial family is Cartesian. -/
theorem endpoint_parameterMap_isPullback {D : Scheme.{u}} (f : D ⟶ X) (c : R) :
    IsPullback (endpoint (f ≫ b) c) f (parameterMap b f) (endpoint b c) where
  w := endpoint_parameterMap b f c
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s ↦ by
    have hf : (s.fst ≫ projection (f ≫ b)) ≫ f = s.snd := by
      have ht := congrArg (fun z ↦ z ≫ projection b) s.condition
      simpa only [Category.assoc, parameterMap_projection, endpoint_projection,
        Category.comp_id] using ht
    refine ⟨s.fst ≫ projection (f ≫ b), ?_, hf, ?_⟩
    · apply pullback.hom_ext
      · change _ ≫ projection (f ≫ b) = _ ≫ projection (f ≫ b)
        simp
      · simp only [PullbackCone.mk_fst]
        rw [Category.assoc, endpoint_snd, ← Category.assoc, ← Category.assoc, hf]
        have ht := congrArg (fun z ↦ z ≫
          pullback.snd b (Spec.map (CommRingCat.ofHom Polynomial.C))) s.condition
        simpa only [Category.assoc, parameterMap_snd, endpoint_snd] using ht.symm
    · intro u hu _
      have ht := congrArg (fun z ↦ z ≫ projection (f ≫ b)) hu
      simpa only [PullbackCone.mk_fst, Category.assoc, endpoint_projection,
        Category.comp_id] using ht)⟩

/-- Pulling any entire support through a Cartesian square preserves the whole fiber. -/
def wholeFiberIso {C D E S T : Scheme.{u}} (j : D ⟶ C) (p : D ⟶ S)
    (q : C ⟶ T) (s : S ⟶ T) (hs : IsPullback j p q s) (i : E ⟶ C) :
    pullback s (i ≫ q) ≅ pullback j i :=
  pullbackSymmetry s (i ≫ q) ≪≫
    (((IsPullback.of_hasPullback j i).flip).paste_vert hs).isoPullback.symm

@[reassoc]
theorem wholeFiberIso_hom_base {C D E S T : Scheme.{u}} (j : D ⟶ C) (p : D ⟶ S)
    (q : C ⟶ T) (s : S ⟶ T) (hs : IsPullback j p q s) (i : E ⟶ C) :
    (wholeFiberIso j p q s hs i).hom ≫ pullback.fst j i ≫ p =
      pullback.fst s (i ≫ q) := by
  simp only [wholeFiberIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    IsPullback.isoPullback_inv_snd, pullbackSymmetry_hom_comp_snd]

@[reassoc]
theorem wholeFiberIso_hom_total {C D E S T : Scheme.{u}} (j : D ⟶ C) (p : D ⟶ S)
    (q : C ⟶ T) (s : S ⟶ T) (hs : IsPullback j p q s) (i : E ⟶ C) :
    (wholeFiberIso j p q s hs i).hom ≫ pullback.snd j i =
      pullback.snd s (i ≫ q) := by
  simp only [wholeFiberIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    IsPullback.isoPullback_inv_fst, pullbackSymmetry_hom_comp_fst]

variable {C : Scheme.{u}} (p : C ⟶ X) (L : C.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible C.sheaf.obj C.ringCatSheaf.property L]
  (a c : Γ(L, ⊤))

/-- The actual map from the whole polynomial zero family to the source cylinder. -/
abbrev familySource := (familyZero (p ≫ b) L a c).subschemeι ≫ parameterMap b p

/-- The zero fiber over the original source is exactly the original zero scheme. -/
def zeroFiberOverBaseIso : pullback (endpoint b 0) (familySource b p L a c) ≅
    (zeroScheme C L a).subscheme :=
  wholeFiberIso (endpoint (p ≫ b) 0) p (parameterMap b p) (endpoint b 0)
    (endpoint_parameterMap_isPullback b p 0) (familyZero (p ≫ b) L a c).subschemeι ≪≫
      zeroFiberIso (p ≫ b) L a c

/-- The one fiber over the original source is exactly the second zero scheme. -/
def oneFiberOverBaseIso : pullback (endpoint b 1) (familySource b p L a c) ≅
    (zeroScheme C L c).subscheme :=
  wholeFiberIso (endpoint (p ≫ b) 1) p (parameterMap b p) (endpoint b 1)
    (endpoint_parameterMap_isPullback b p 1) (familyZero (p ≫ b) L a c).subschemeι ≪≫
      oneFiberIso (p ≫ b) L a c

@[reassoc]
theorem zeroFiberOverBaseIso_hom_base :
    (zeroFiberOverBaseIso b p L a c).hom ≫ (zeroScheme C L a).subschemeι ≫ p =
      pullback.fst (endpoint b 0) (familySource b p L a c) := by
  simp only [zeroFiberOverBaseIso, Iso.trans_hom, Category.assoc,
    zeroFiberIso_hom_inclusion_assoc, wholeFiberIso_hom_base]

@[reassoc]
theorem oneFiberOverBaseIso_hom_base :
    (oneFiberOverBaseIso b p L a c).hom ≫ (zeroScheme C L c).subschemeι ≫ p =
      pullback.fst (endpoint b 1) (familySource b p L a c) := by
  simp only [oneFiberOverBaseIso, Iso.trans_hom, Category.assoc,
    oneFiberIso_hom_inclusion_assoc, wholeFiberIso_hom_base]

@[reassoc]
theorem zeroFiberOverBaseIso_hom_original :
    (zeroFiberOverBaseIso b p L a c).hom ≫ (zeroScheme C L a).subschemeι =
      pullback.snd (endpoint b 0) (familySource b p L a c) ≫
        (familyZero (p ≫ b) L a c).subschemeι ≫ projection (p ≫ b) := by
  simp only [zeroFiberOverBaseIso, Iso.trans_hom, Category.assoc,
    zeroFiberIso_hom_total, wholeFiberIso_hom_total_assoc]

@[reassoc]
theorem oneFiberOverBaseIso_hom_original :
    (oneFiberOverBaseIso b p L a c).hom ≫ (zeroScheme C L c).subschemeι =
      pullback.snd (endpoint b 1) (familySource b p L a c) ≫
        (familyZero (p ≫ b) L a c).subschemeι ≫ projection (p ≫ b) := by
  simp only [oneFiberOverBaseIso, Iso.trans_hom, Category.assoc,
    oneFiberIso_hom_total, wholeFiberIso_hom_total_assoc]

end AlgebraicGeometry.Scheme.PolynomialSectionPencil
