/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.PointSupport
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Gersten.SmoothStratum
import Colib.AlgebraicGeometry.Scheme.CartesianRange

/-! # The original smooth models in the point-support diagram -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
open TopologicalSpace Opposite AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.MotivicHomotopy Stacks.Chow

universe u

namespace AlgebraicGeometry.SheafWithTransfers.Gersten

variable {k : Type u} [Field k] {X : SmoothSite (Spec (CommRingCat.of k))} {x : X.left}
  {U₀ : PointSupportNeighborhoods k X x}
  (h₀ : Smooth ((pointClosureInclusion k X x ∣_ U₀.1) ≫
    (Scheme.Opens.ι (X := X.left) U₀.1 ≫ X.hom)))

local notation "Sm" => SmoothSite (Spec (CommRingCat.of k))
local notation "I" => Set.Iic U₀
local notation "Z₀" => smoothPointClosure h₀
set_option quotPrecheck false in
local notation "q" => (pointClosureOpen k X x U₀.1).ι

include h₀ in
/-- The smooth reduced closure also gives a smooth model on every subneighborhood. -/
theorem smoothPointClosureOn (U : I) :
    Smooth ((pointClosureInclusion k X x ∣_ U.1.1) ≫
      (Scheme.Opens.ι (X := X.left) U.1.1 ≫ X.hom)) :=
  smooth_pointClosure_of_le h₀ U.2

/-- The actual reduced point closures on the smooth subneighborhoods. -/
def smoothPointCenterFunctor : I ⥤ Sm where
  obj U := smoothPointClosure (smoothPointClosureOn h₀ U)
  map {U V} a := smoothPointClosureMap (smoothPointClosureOn h₀ U) (smoothPointClosureOn h₀ V) a.le
  map_id U := by
    apply MorphismProperty.Over.Hom.ext
    exact Scheme.homOfLE_rfl _ _
  map_comp {U V W} a b := by
    apply MorphismProperty.Over.Hom.ext
    let i := pointClosureInclusion k X x
    exact (Scheme.homOfLE_homOfLE (pointClosure k X x)
      (i.preimage_mono (show U.1.1 ≤ V.1.1 from a.le))
      (i.preimage_mono (show V.1.1 ≤ W.1.1 from b.le))).symm

/-- The marked point of the smooth model is the generic point of the reduced closure. -/
abbrev smoothPointCenterGeneric : (Z₀).left :=
  pointClosureGeneric k X x U₀.1 U₀.2

/-- Restriction from the smooth reduced closure into the chosen model. -/
abbrev smoothPointCenterInclusion (U : I) :
    (smoothPointCenterFunctor h₀).obj U ⟶ Z₀ :=
  smoothPointClosureMap (smoothPointClosureOn h₀ U) h₀ U.2

instance (U : I) : IsOpenImmersion (smoothPointCenterInclusion h₀ U).left :=
  inferInstanceAs (IsOpenImmersion
    ((pointClosure k X x).homOfLE ((pointClosureInclusion k X x).preimage_mono U.2)))

instance (U V : I) (a : U ⟶ V) :
    IsOpenImmersion ((smoothPointCenterFunctor h₀).map a).left :=
  inferInstanceAs (IsOpenImmersion ((pointClosure k X x).homOfLE
    ((pointClosureInclusion k X x).preimage_mono (show U.1.1 ≤ V.1.1 from a.le))))

instance (U V : I) (a : U ⟶ V) :
    IsOpenImmersion ((opensFunctor X).map (homOfLE (show U.1.1 ≤ V.1.1 from a.le))).left :=
  inferInstanceAs (IsOpenImmersion (X.left.homOfLE (show U.1.1 ≤ V.1.1 from a.le)))

/-- Sending an ambient subneighborhood to its inverse image in the smooth model
gives an open neighborhood of the generic point in that model. -/
def smoothPointCenterNeighborhoods :
    I ⥤ OpenNhds (X := (Z₀).left.carrier) (smoothPointCenterGeneric h₀) where
  obj U := ⟨(q) ⁻¹ᵁ pointClosureOpen k X x U.1.1, by
    change pointClosureInclusion k X x (genericPoint (pointClosure k X x)) ∈ U.1.1
    rw [show pointClosureInclusion k X x (genericPoint (pointClosure k X x)) = x from
      genericPointOf_integralComponentAt x]
    exact U.1.2⟩
  map a := homOfLE ((q).preimage_mono ((pointClosureInclusion k X x).preimage_mono a.le))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The ambient subneighborhoods are cofinal among the opens of the model
containing its generic point. -/
instance : (smoothPointCenterNeighborhoods h₀).op.Final := by
  rw [Functor.final_iff_of_isFiltered]
  constructor
  · intro W
    let A : (pointClosure k X x).Opens := (q) ''ᵁ W.unop.1
    have hη : genericPoint (pointClosure k X x) ∈ A :=
      ⟨smoothPointCenterGeneric h₀, W.unop.2, rfl⟩
    obtain ⟨U, hx, hU⟩ := exists_open_preimage_pointClosure k X x A hη
    let V₀ : PointSupportNeighborhoods k X x := ⟨U ⊓ U₀.1, hx, U₀.2⟩
    have hVU₀ : V₀ ≤ U₀ := (OpenNhds.le_def V₀ U₀).2 inf_le_right
    let V : I := ⟨V₀, Set.mem_Iic.mpr hVU₀⟩
    have hv : ((smoothPointCenterNeighborhoods h₀).obj V).1 ≤ W.unop.1 := by
      change (q) ⁻¹ᵁ pointClosureOpen k X x (U ⊓ U₀.1) ≤ W.unop.1
      have hpre := congrArg (fun B : (pointClosure k X x).Opens => (q) ⁻¹ᵁ B) hU
      exact ((q).preimage_mono ((pointClosureInclusion k X x).preimage_mono inf_le_left)).trans_eq
        (hpre.trans ((q).preimage_image_eq W.unop.1))
    exact ⟨op V, ⟨(homOfLE hv).op⟩⟩
  · intro _ V _ _
    exact ⟨V, 𝟙 _, Subsingleton.elim _ _⟩

private def smoothPointCenterOpenData (U : I) :
    { e : (smoothPointCenterFunctor h₀).obj U ≅
        (opensFunctor (Z₀)).obj ((smoothPointCenterNeighborhoods h₀).obj U).1 //
      e.hom ≫ openInclusion (Z₀) ((smoothPointCenterNeighborhoods h₀).obj U).1 =
        smoothPointCenterInclusion h₀ U } := by
  let f := smoothPointCenterInclusion h₀ U
  let W : (Z₀).left.Opens := ((smoothPointCenterNeighborhoods h₀).obj U).1
  let j := openInclusion (Z₀) W
  letI : IsOpenImmersion f.left := inferInstanceAs
    (IsOpenImmersion (smoothPointCenterInclusion h₀ U).left)
  letI : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion W.ι)
  have hw : f.left.opensRange = j.left.opensRange := by
    let i := pointClosureInclusion k X x
    change ((pointClosure k X x).homOfLE (i.preimage_mono U.2)).opensRange = W.ι.opensRange
    exact (Scheme.opensRange_homOfLE (i.preimage_mono U.2)).trans
      (Scheme.Opens.opensRange_ι W).symm
  let R := (congrArg (fun W : (Z₀).left.Opens => (W : Set (Z₀).left)) hw)
  let e := IsOpenImmersion.isoOfRangeEq f.left j.left R
  have he : e.hom ≫ j.left = f.left := IsOpenImmersion.isoOfRangeEq_hom_fac f.left j.left R
  let e' : (smoothPointCenterFunctor h₀).obj U ≅ (opensFunctor (Z₀)).obj W :=
    MorphismProperty.Over.isoMk e (by
      rw [← MorphismProperty.Over.w j, ← Category.assoc, he, MorphismProperty.Over.w f])
  exact ⟨e', MorphismProperty.Over.Hom.ext he⟩

/-- The actual smooth centre over an ambient subneighborhood is its open
subscheme in the chosen smooth model. -/
@[no_expose]
def smoothPointCenterOpenIso (U : I) :
    (smoothPointCenterFunctor h₀).obj U ≅
      (opensFunctor (Z₀)).obj ((smoothPointCenterNeighborhoods h₀).obj U).1 :=
  (smoothPointCenterOpenData h₀ U).1

/-- The chart comparison preserves the original inclusions into the chosen model. -/
@[reassoc]
theorem smoothPointCenterOpenIso_hom_comp (U : I) :
    (smoothPointCenterOpenIso h₀ U).hom ≫
        openInclusion (Z₀) ((smoothPointCenterNeighborhoods h₀).obj U).1 =
      smoothPointCenterInclusion h₀ U :=
  (smoothPointCenterOpenData h₀ U).2

/-- The centre diagram of the smooth ambient subneighborhoods is the cofinal
restriction of the ordinary open-neighborhood diagram of its generic point. -/
def smoothPointCenterFunctorIso :
    smoothPointCenterFunctor h₀ ≅ smoothPointCenterNeighborhoods h₀ ⋙
      OpenNhds.inclusion (smoothPointCenterGeneric h₀) ⋙ opensFunctor (Z₀) :=
  NatIso.ofComponents (smoothPointCenterOpenIso h₀) (fun {U V} a => by
    let A : (Z₀).left.Opens := ((smoothPointCenterNeighborhoods h₀).obj U).1
    let B : (Z₀).left.Opens := ((smoothPointCenterNeighborhoods h₀).obj V).1
    let j := openInclusion (Z₀) B
    let : Mono j := (forgetScheme _).mono_of_mono_map (inferInstanceAs (Mono B.ι))
    let eU := smoothPointCenterOpenIso h₀ U
    let eV := smoothPointCenterOpenIso h₀ V
    let g := (smoothPointCenterFunctor h₀).map a
    let G := smoothPointCenterNeighborhoods h₀ ⋙
      OpenNhds.inclusion (smoothPointCenterGeneric h₀) ⋙ opensFunctor (Z₀)
    let g' := G.map a
    have hAB : A ≤ B := ((smoothPointCenterNeighborhoods h₀).map a).le
    have hcomp : g' ≫ j = openInclusion (Z₀) A :=
      MorphismProperty.Over.Hom.ext (Scheme.homOfLE_ι (Z₀).left hAB)
    have hcent : g ≫ smoothPointCenterInclusion h₀ V = smoothPointCenterInclusion h₀ U :=
      MorphismProperty.Over.Hom.ext (Scheme.homOfLE_homOfLE (pointClosure k X x)
        ((pointClosureInclusion k X x).preimage_mono (show U.1.1 ≤ V.1.1 from a.le))
        ((pointClosureInclusion k X x).preimage_mono V.2))
    have hleft : (g ≫ eV.hom) ≫ j = smoothPointCenterInclusion h₀ U :=
      (Category.assoc _ _ _).trans
        ((congrArg (g ≫ ·) (smoothPointCenterOpenIso_hom_comp h₀ V)).trans hcent)
    have hright : (eU.hom ≫ g') ≫ j = smoothPointCenterInclusion h₀ U :=
      (Category.assoc _ _ _).trans
        ((congrArg (eU.hom ≫ ·) hcomp).trans (smoothPointCenterOpenIso_hom_comp h₀ U))
    exact (cancel_mono j).1 (hleft.trans hright.symm))

/-- The closed immersion of the smooth reduced closure has the actual restricted
topological closure as its support. -/
theorem range_smoothPointClosureInclusion (U : I) :
    Set.range (smoothPointClosureInclusion (smoothPointClosureOn h₀ U)).left =
      Scheme.Opens.ι (X := X.left) U.1.1 ⁻¹' closure {x} := by
  let i := pointClosureInclusion k X x
  change Set.range (i ∣_ U.1.1) = _
  have hi : Set.range i = closure {x} := by
    change Set.range ((integralComponentAt x).subschemeι) = _
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]
  exact (Scheme.range_fst_of_isPullback (isPullback_morphismRestrict i U.1.1)).trans
    (congrArg (fun T : Set X.left => Scheme.Opens.ι (X := X.left) U.1.1 ⁻¹' T) hi)

/-- The function field at the marked generic point of the smooth model is the
residue field of the original point. -/
def smoothPointCenterResidueIso :
    X.left.residueField x ≅ (Z₀).left.residueField (smoothPointCenterGeneric h₀) := by
  let i := (smoothPointClosureInclusion h₀).left
  let z := smoothPointCenterGeneric h₀
  let j := Scheme.Opens.ι (X := X.left) U₀.1
  have hz : j (i z) = x :=
    congrArg j (pointClosureInclusion_restrict_generic U₀.1 U₀.2)
  letI : IsOpenImmersion j := inferInstanceAs
    (IsOpenImmersion (Scheme.Opens.ι (X := X.left) U₀.1))
  letI : IsIso (j.residueFieldMap (i z)) := inferInstance
  let e := RingEquiv.ofBijective (i.residueFieldMap z).hom
    (bijective_residueFieldMap_of_isClosedImmersion i z)
  exact eqToIso (congrArg X.left.residueField hz.symm) ≪≫
    asIso (j.residueFieldMap (i z)) ≪≫ e.toCommRingCatIso

end AlgebraicGeometry.SheafWithTransfers.Gersten
