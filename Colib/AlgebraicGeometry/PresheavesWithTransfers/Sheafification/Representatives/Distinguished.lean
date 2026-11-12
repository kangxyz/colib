/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.Representatives.Basic
public import Colib.AlgebraicGeometry.Sites.Nisnevich.MonicRefinement
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.LineOpenMaps
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.DistinguishedSquare


/-!
# Matching unit-image representatives on a distinguished cover

A singleton representative of the section is pulled back along the
original monic refinement of the polynomial cylinder. The two pieces
retain their matching equation, their actual unit images and the finite
closed complement over the same restricted base.

Adapted from Motivic at a6805c4a87cdfd7717dd7a94039246a167f15380,
Motivic/Transfers/Presheaf/Sheafification/Representatives/Distinguished.lean.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.PolynomialOpenQuotient
open AlgebraicGeometry.Scheme.SmoothSite.Contraction
open _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineCoordinates
  _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineSectionCoordinates
  _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite

universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable {k : Type u} [Field k]
local notation "π" => projection (SmoothSite.additiveGroupObject (Spec (CommRingCat.of k)))
attribute [local instance] sectionsAlgebra

/-- A section of the original sheafification gives two matching unit-image
representatives on a distinguished cover of the restricted cylinder. -/
theorem exists_affine_open_distinguished_nisnevichImage_representatives
    (P : PresheafWithTransfers.{u + 1} k)
    (X : SmoothSite (Spec (.of k))) [IsAffine X.left] [IsIntegral X.left]
    (g : ((nisnevichSheafify k).obj P).obj.sections
      (Cor.mk (affineLineCylinder.obj X))) :
    ∃ (U : SmoothSite (Spec (.of k))) (j : U ⟶ X),
      IsOpenImmersion j.left ∧ Nonempty U.left ∧ IsAffine U.left ∧
      ∃ (T : SmoothSite (Spec (.of k))) (e : T ≅ affineLineCylinder.obj U)
        (A V : SmoothSite (Spec (.of k))) (i : A ⟶ T) (v : V ⟶ T),
        IsAffine A.left ∧ IsOpenImmersion i.left ∧ Etale v.left ∧
        Sieve.ofTwoArrows i v ∈ SmoothSite.nisnevichTopology (Spec (.of k)) T ∧
        ∃ (Z : Scheme.{u}) (z : Z ⟶ T.left), IsClosedImmersion z ∧
          IsFinite (z ≫ e.hom.left ≫ ((π).app U).left) ∧
          Set.range z = (Set.range i.left)ᶜ ∧ IsIso (pullback.snd v.left z) ∧
          ∃ (B : SmoothSite (Spec (.of k))) (bA : B ⟶ A) (bV : B ⟶ V),
            IsPullback bA bV i v ∧
            ∃ (sA : (nisnevichImage P).sections (Cor.mk A))
              (sV : (nisnevichImage P).sections (Cor.mk V)),
              (nisnevichImage P).transfer ((Cor.graphFunctor k).map bA) sA =
                (nisnevichImage P).transfer ((Cor.graphFunctor k).map bV) sV ∧
              (nisnevichImageι P).hom.app (op (Cor.mk A)) sA =
                ((nisnevichSheafify k).obj P).obj.transfer
                  ((Cor.graphFunctor k).map (i ≫ e.hom ≫ affineLineCylinder.map j)) g ∧
              (nisnevichImageι P).hom.app (op (Cor.mk V)) sV =
                ((nisnevichSheafify k).obj P).obj.transfer
                  ((Cor.graphFunctor k).map (v ≫ e.hom ≫ affineLineCylinder.map j)) g := by
  let R := Γ(X.left, ⊤)
  let L := _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite.lineSite (k := k) (R := R)
  let eX := affineLineIso X
  let G := ((nisnevichSheafify k).obj P).obj
  let S := nisnevichImage P
  let gL := G.transfer ((Cor.graphFunctor k).map eX.hom) g
  obtain ⟨Y, q, hq, tY, htY, hmatch⟩ := exists_nisnevichImage_representing_cover P L gL
  have hq' : Presieve.singleton q.left ∈ _root_.AlgebraicGeometry.Nisnevich.precoverage L.left := by
    apply Nisnevich.mem_precoverage_iff.mpr
    constructor
    · intro Q f hf
      cases hf
      exact hq.1
    · intro x
      obtain ⟨y, hy, hy'⟩ := hq.2 x
      exact ⟨Y.left, q.left, Presieve.singleton_self q.left, y, hy, hy'⟩
  obtain ⟨r, hr, p, hp, t, ht, V₀, v₀, a₀, hv₀, ha₀, hvq, hVz, s₀, hs₀⟩ :=
    _root_.AlgebraicGeometry.Nisnevich.exists_monic_refinement R q.left hq'
  let R₁ := Localization.Away r
  let : IsDomain R₁ := Localization.Away.isDomain hr
  let : Algebra.Smooth R R₁ := Algebra.Smooth.of_isLocalization_Away r
  let : Algebra.Smooth k R₁ := Algebra.Smooth.comp k R R₁
  let R₂ := Localization.Away t
  let : IsDomain R₂ := Localization.Away.isDomain ht
  let : Algebra.Smooth R₁ R₂ := Algebra.Smooth.of_isLocalization_Away t
  let : Algebra.Smooth k R₂ := Algebra.Smooth.comp k R₁ R₂
  let φ₁ := IsScalarTower.toAlgHom k R R₁
  let φ₂ := IsScalarTower.toAlgHom k R₁ R₂
  let U := _root_.AlgebraicGeometry.Scheme.SmoothSite.affineSite k R₂
  let j := _root_.AlgebraicGeometry.Scheme.SmoothSite.affineMorphism φ₂ ≫
      _root_.AlgebraicGeometry.Scheme.SmoothSite.affineMorphism φ₁ ≫ (affineIso X).hom
  let : IsOpenImmersion (_root_.AlgebraicGeometry.Scheme.SmoothSite.affineMorphism φ₁).left :=
      IsOpenImmersion.of_isLocalization r
  let : IsOpenImmersion (_root_.AlgebraicGeometry.Scheme.SmoothSite.affineMorphism φ₂).left :=
      IsOpenImmersion.of_isLocalization t
  let T := _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite.lineSite (k := k) (R := R₂)
  let e := lineCylinderIso (k := k) (R := R₂)
  let b := _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite.lineMap φ₂ ≫
      _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite.lineMap φ₁
  have hb : b ≫ eX.hom = e.hom ≫ affineLineCylinder.map j := by
    dsimp only [b, e, eX, affineLineIso, Iso.trans_hom, cylinderIso, j]
    simp only [Category.assoc, lineCylinderIso_naturality_assoc,
      Functor.map_comp, Functor.mapIso_hom]
  let f := p.map (algebraMap R₁ R₂)
  let : Etale v₀ := hv₀
  let : IsOpenImmersion a₀ := ha₀
  have hbase : a₀ ≫ Y.hom = v₀ ≫ T.hom := by
    rw [← MorphismProperty.Over.w q, ← Category.assoc, hvq, Category.assoc]
    exact congrArg (fun h => v₀ ≫ h) (MorphismProperty.Over.w b)
  let V := SmoothSite.mk (a₀ ≫ Y.hom)
  let v : V ⟶ T := SmoothSite.homMk v₀ hbase.symm
  let : Etale v.left := hv₀
  let aV : V ⟶ Y := SmoothSite.homMk a₀ rfl
  let A := _root_.AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite.originalOpenSite (k := k)
      (principalOpen f)
  have hAa : IsAffine A.left := by
    change IsAffineOpen (principalOpen f)
    exact IsAffineOpen.Spec_basicOpen (R := .of (Polynomial R₂)) f
  let i : A ⟶ T := SmoothSite.homMk (principalOpen f).ι rfl
  let : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion (principalOpen f).ι)
  have hsbase : s₀ ≫ Y.hom = (principalOpen f).ι ≫ T.hom := by
    rw [← MorphismProperty.Over.w q, ← Category.assoc, hs₀, Category.assoc]
    exact congrArg (fun h => (principalOpen f).ι ≫ h) (MorphismProperty.Over.w b)
  let aA : A ⟶ Y := SmoothSite.homMk s₀ hsbase
  have hAv : aA ≫ q = i ≫ b := by
    apply MorphismProperty.Over.Hom.ext
    exact hs₀
  have hVv : aV ≫ q = v ≫ b := by
    apply MorphismProperty.Over.Hom.ext
    exact hvq
  let z := inclusion f
  let : IsIso (pullback.snd v.left z) := hVz
  have hcomp : Set.range z = (Set.range i.left)ᶜ := by
    change Set.range (inclusion f) = (Set.range (principalOpen f).ι)ᶜ
    rw [Scheme.Opens.range_ι]
    exact range_inclusion_complement f
  have hcover := SmoothSite.ofTwoArrows_mem_nisnevichTopology_of_iso_complement i v z hcomp
  have hfin : IsFinite (z ≫ e.hom.left ≫ ((π).app U).left) := by
    have he := congrArg (fun h => h.left) (lineCylinderIso_projection (k := k) (R := R₂))
    change IsFinite (z ≫ (e.hom ≫ (π).app U).left)
    rw [he]
    change IsFinite (inclusion f ≫
      AlgebraicGeometry.Scheme.PolynomialLaurent.polynomialProjection (.of R₂))
    rw [inclusion_projection]
    exact source_finite f (hp.map _)
  let B := pullback i v
  let bA := pullback.fst i v
  let bV := pullback.snd i v
  let sA := S.transfer ((Cor.graphFunctor k).map aA) tY
  let sV := S.transfer ((Cor.graphFunctor k).map aV) tY
  have hm : S.transfer ((Cor.graphFunctor k).map bA) sA =
      S.transfer ((Cor.graphFunctor k).map bV) sV := by
    have hc : (bA ≫ aA) ≫ q = (bV ≫ aV) ≫ q := by
      simp only [Category.assoc, hAv, hVv]
      simpa only [Category.assoc] using
        congrArg (fun h => h ≫ b) (pullback.condition (f := i) (g := v))
    have hh := hmatch B (bA ≫ aA) (bV ≫ aV) hc
    simpa only [Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply] using hh
  have hu (D : SmoothSite (Spec (.of k))) (d : D ⟶ Y) (c : D ⟶ T)
      (hd : d ≫ q = c ≫ b) :
      (nisnevichImageι P).hom.app (op (Cor.mk D))
          (S.transfer ((Cor.graphFunctor k).map d) tY) =
        G.transfer ((Cor.graphFunctor k).map (c ≫ e.hom ≫ affineLineCylinder.map j)) g := by
    have hn : (nisnevichImageι P).hom.app (op (Cor.mk D))
        (S.transfer ((Cor.graphFunctor k).map d) tY) =
        G.transfer ((Cor.graphFunctor k).map d)
          ((nisnevichImageι P).hom.app (op (Cor.mk Y)) tY) :=
      (nisnevichImageι P).hom.naturality_apply ((Cor.graphFunctor k).map d).op tY
    rw [hn, htY]
    have heq : d ≫ q ≫ eX.hom = c ≫ e.hom ≫ affineLineCylinder.map j := by
      rw [← Category.assoc, hd, Category.assoc, hb]
    have hh := congrArg (fun m => G.transfer ((Cor.graphFunctor k).map m) g) heq
    simpa only [Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply] using hh
  have hj : IsOpenImmersion j.left := by
    change IsOpenImmersion ((_root_.AlgebraicGeometry.Scheme.SmoothSite.affineMorphism φ₂).left ≫
      (_root_.AlgebraicGeometry.Scheme.SmoothSite.affineMorphism φ₁).left ≫ (affineIso X).hom.left)
    infer_instance
  have hUn : Nonempty U.left := inferInstanceAs (Nonempty (Spec (.of R₂)))
  have hUa : IsAffine U.left := inferInstanceAs (IsAffine (Spec (.of R₂)))
  exact ⟨U, j, hj, hUn, hUa, T, e, A, V, i, v,
    hAa, inferInstance, inferInstance, hcover, _, z, inferInstance, hfin, hcomp,
    inferInstance, B, bA, bV, IsPullback.of_hasPullback i v, sA, sV, hm,
    hu A aA i hAv, hu V aV v hVv⟩

end AlgebraicGeometry.PresheafWithTransfers
