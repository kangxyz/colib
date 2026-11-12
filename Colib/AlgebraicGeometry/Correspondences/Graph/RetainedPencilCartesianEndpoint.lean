/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.RetainedPencilSpans

/-!
# Cartesian endpoints of the whole retained polynomial family

The actual paired support specializes to its Cartesian affine-section fiber.
The native zero and one support isomorphisms carry its finite-flat source leg
onto the full original zero schemes.
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

/-- Specialization of a whole correspondence along the actual affine section. -/
def NativeSectionSpanSpecialization {k : Type u} [Field k]
    (U W : SmoothSite (Spec (.of k))) (s : k)
    (δ : finiteCorrespondences (affineLineCylinder.obj U).hom W.hom)
    (η : finiteCorrespondences U.hom W.hom) : Prop :=
  (graphFunctor k).map (nativeAffineSection (.of k) U s) ≫
    (show Cor.mk (affineLineCylinder.obj U) ⟶ Cor.mk W from δ) = η

/-- The underlying graph-precomposition equation on the original objects. -/
theorem NativeSectionSpanSpecialization.eq {k : Type u} [Field k]
    {U W : SmoothSite (Spec (.of k))} {s : k}
    {δ : finiteCorrespondences (affineLineCylinder.obj U).hom W.hom}
    {η : finiteCorrespondences U.hom W.hom}
    (h : NativeSectionSpanSpecialization U W s δ η) :
    (graphFunctor k).map (nativeAffineSection (.of k) U s) ≫
      (show Cor.mk (affineLineCylinder.obj U) ⟶ Cor.mk W from δ) = η := h

/-- Change the fiber span by an equality of the actual correspondences. -/
theorem NativeSectionSpanSpecialization.congr_right {k : Type u} [Field k]
    {U W : SmoothSite (Spec (.of k))} {s : k}
    {δ : finiteCorrespondences (affineLineCylinder.obj U).hom W.hom}
    {η η' : finiteCorrespondences U.hom W.hom}
    (h : NativeSectionSpanSpecialization U W s δ η) (e : η = η') :
    NativeSectionSpanSpecialization U W s δ η' := e ▸ h

/-- The actual first and second paired projections specialize to the whole Cartesian fiber. -/
theorem nativeSection_comp_span_legs {k : Type u} [Field k] {D : Scheme.{u}}
    (U W : SmoothSite (Spec (.of k))) (s : k)
    (m : D ⟶ pullback (affineLineCylinder.obj U).hom W.hom) [IsClosedImmersion m]
    (f : D ⟶ (affineLineCylinder.obj U).left) (g : D ⟶ W.left)
    (hfFin : IsFinite f) (hfFlat : Flat f)
    (hf : m ≫ pullback.fst (affineLineCylinder.obj U).hom W.hom = f)
    (hg : m ≫ pullback.snd (affineLineCylinder.obj U).hom W.hom = g)
    (hFam : f ≫ (affineLineCylinder.obj U).hom = g ≫ W.hom)
    (h : pullback.fst (nativeAffineSection (.of k) U s).left f ≫ U.hom =
      (pullback.snd (nativeAffineSection (.of k) U s).left f ≫ g) ≫ W.hom) :
    letI : IsNoetherian ((𝟭 Scheme).obj (affineLineCylinder.obj U).left) :=
      inferInstanceAs (IsNoetherian (affineLineCylinder.obj U).left)
    NativeSectionSpanSpecialization U W s
      (ofFiniteFlatSpanRaw (affineLineCylinder.obj U).hom W.hom f
        (hFin := hfFin) (hFlat := hfFlat) g hFam)
      (letI : IsNoetherian ((𝟭 Scheme).obj U.left) := inferInstanceAs (IsNoetherian U.left)
       cartesianEndpointSpan U.hom W.hom (nativeAffineSection (.of k) U s).left f g
         hfFin hfFlat h) := by
  have : IsFinite (m ≫ pullback.fst (affineLineCylinder.obj U).hom W.hom) :=
    isFinite_of_spanLeg_eq hf hfFin
  have : Flat (m ≫ pullback.fst (affineLineCylinder.obj U).hom W.hom) :=
    flat_of_spanLeg_eq hf hfFlat
  subst f
  subst g
  unfold NativeSectionSpanSpecialization
  exact nativeSection_comp_ofFiniteFlatSpan_pair U W s m

variable {k : Type u} [Field k] {S X V : Scheme.{u}}
  (t : S ⟶ Spec (.of k)) (q : X ⟶ S) (r : V ⟶ S)
  [Smooth (q ≫ t)] [IsSeparated (q ≫ t)] [QuasiCompact (q ≫ t)]
  (L : (pullback q r).Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback q r).sheaf.obj
    (pullback q r).ringCatSheaf.property L] (a c : Γ(L, ⊤))

local notation "U" => SmoothSite.mk (q ≫ t)
local notation "F" => nativeRetainedFamilySource t q r L a c

/-- The complete original zero fiber inherits finiteness and flatness. -/
theorem nativeRetainedZero_finite_flat :
    let f := F
    ∀ [_hFamilyFin : IsFinite f] [_hFamilyFlat : Flat f],
      IsFinite ((zeroScheme (pullback q r) L a).subschemeι ≫ pullback.fst q r) ∧
        Flat ((zeroScheme (pullback q r) L a).subschemeι ≫ pullback.fst q r) := by
  intro f hFin hFlat
  let σ := (nativeAffineSection (.of k) U 0).left
  let Z := (zeroScheme (pullback q r) L a).subscheme
  let g : Z ⟶ X := (zeroScheme (pullback q r) L a).subschemeι ≫ pullback.fst q r
  let e : pullback σ f ≅ Z := nativeZeroFiberIso U (pullback.fst q r) L a c
  have he : e.hom ≫ g = pullback.fst σ f :=
    nativeZeroFiberIso_hom_base U (pullback.fst q r) L a c
  exact @finiteFlat_of_cartesian_support_iso X (affineLineCylinder.obj U).left
    (familyZero (pullback.fst q r ≫ (q ≫ t)) L a c).subscheme Z σ f g e he hFin hFlat

/-- The complete original one fiber inherits finiteness and flatness. -/
theorem nativeRetainedOne_finite_flat :
    let f := F
    ∀ [_hFamilyFin : IsFinite f] [_hFamilyFlat : Flat f],
      IsFinite ((zeroScheme (pullback q r) L c).subschemeι ≫ pullback.fst q r) ∧
        Flat ((zeroScheme (pullback q r) L c).subschemeι ≫ pullback.fst q r) := by
  intro f hFin hFlat
  let σ := (nativeAffineSection (.of k) U 1).left
  let Z := (zeroScheme (pullback q r) L c).subscheme
  let g : Z ⟶ X := (zeroScheme (pullback q r) L c).subschemeι ≫ pullback.fst q r
  let e : pullback σ f ≅ Z := nativeOneFiberIso U (pullback.fst q r) L a c
  have he : e.hom ≫ g = pullback.fst σ f :=
    nativeOneFiberIso_hom_base U (pullback.fst q r) L a c
  exact @finiteFlat_of_cartesian_support_iso X (affineLineCylinder.obj U).left
    (familyZero (pullback.fst q r ≫ (q ≫ t)) L a c).subscheme Z σ f g e he hFin hFlat

end AlgebraicGeometry.Cor
