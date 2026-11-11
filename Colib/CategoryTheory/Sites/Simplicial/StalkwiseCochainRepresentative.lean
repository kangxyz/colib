/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicTopology.DoldKan.CochainRepresentative.Homotopy
public import Colib.CategoryTheory.Localization.Representability
public import Colib.CategoryTheory.Sites.Simplicial.KInjectiveRepresentativeMaps
public import Colib.CategoryTheory.Sites.Simplicial.ReducedCylinderChains
public import Colib.CategoryTheory.Sites.Simplicial.SimplicialCylinder
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseDerivedChains

/-!
# Stalkwise representation by the actual pointed cochain representative

Equality of strict derived classes for a K-injective coefficient produces
a cochain homotopy. Good truncation and the actual pointed simplicial
cylinder realize this homotopy before stalkwise localization. When reduced
chains invert the stalkwise class, the strict-map comparison represents
reduced hypercohomology in that localization.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe d w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] [LocallySmall.{w} C]
  (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (Sheaf J AddCommGrpCat.{w})]

/-- Strict maps with the same K-injective derived class agree in the stalkwise localization. -/
theorem toStalkwiseHomotopyCategory_map_eq_of_derivedMap_eq
    (p : ℤ) (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) [K.IsKInjective]
    (X : PointedSimplicialPresheaf.{w} C) (f g : X ⟶ (pointedCochainRepresentative C J p).obj K)
    (h : pointedCochainRepresentativeDerivedMap C J p K X f =
      pointedCochainRepresentativeDerivedMap C J p K X g) :
    (toStalkwiseHomotopyCategory C J).map f = (toStalkwiseHomotopyCategory C J).map g := by
  obtain ⟨H⟩ := (pointedCochainRepresentativeDerivedMap_eq_iff C J p K X f g).mp h
  let N := sheafifiedReducedChains.{w} C J
  let P := N.obj X
  let L := (CochainComplex.shiftedNonpositiveChains _ p).obj K
  let A := reducedChainsForgetAdjunction.{w} C J
  let e := CochainComplex.shiftedNonpositiveChainsHomEquiv (Sheaf J AddCommGrpCat.{w}) p K P
  have H' := CochainComplex.shiftedNonpositiveChainsHomEquivHomotopy
    (Sheaf J AddCommGrpCat.{w}) p K P H
  change Homotopy (e (e.symm ((A.homEquiv X L).symm f)))
    (e (e.symm ((A.homEquiv X L).symm g))) at H'
  rw [e.apply_symm_apply, e.apply_symm_apply] at H'
  let m := sheafifiedReducedCylinderChainsMap X J H'
  let Z := parameterizedCylinder X (interval C)
  let s : Z ⟶ (pointedCochainRepresentative C J p).obj K := (A.homEquiv Z L) m
  let s₀ := cylinderSection X (intervalEndpoint C (1 : Fin 2))
  let s₁ := cylinderSection X (intervalEndpoint C (0 : Fin 2))
  have hs₀ : s₀ ≫ s = f :=
    (A.homEquiv_naturality_left s₀ m).symm.trans
      ((congrArg (A.homEquiv X L) (sheafifiedReducedCylinderChainsMap_zero X J H')).trans
        ((A.homEquiv X L).apply_symm_apply f))
  have hs₁ : s₁ ≫ s = g :=
    (A.homEquiv_naturality_left s₁ m).symm.trans
      ((congrArg (A.homEquiv X L) (sheafifiedReducedCylinderChainsMap_one X J H')).trans
        ((A.homEquiv X L).apply_symm_apply g))
  rw [← hs₀, ← hs₁]
  exact toStalkwiseHomotopyCategory_map_of_simplicialCylinder C J s 1 0

variable [J.HasEnoughPoints.{w}]

/-- Under realization invariance of the chosen reduced chains, the actual
K-injective pointed representative computes reduced hypercohomology in the
stalkwise localization. -/
def stalkwiseCochainRepresentativeHomEquiv
    (h : PointedSimplicialSetChainsPreserveRealizationWeakEquivalences.{w})
    (p : ℤ) (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) [K.IsKInjective]
    (X : PointedSimplicialPresheaf.{w} C) :
    ((toStalkwiseHomotopyCategory C J).obj X ⟶
      (toStalkwiseHomotopyCategory C J).obj ((pointedCochainRepresentative C J p).obj K)) ≃
      (reducedHypercohomology C J K p).obj (op X) := by
  let Q := toStalkwiseHomotopyCategory.{w} C J
  let D := stalkwiseReducedDerivedChains C J h
  let τ := stalkwiseReducedDerivedChainsFactors C J h
  let T := (DerivedCategory.Q.obj K)⟦p⟧
  let F : (StalkwiseHomotopyCategory.{w} C J)ᵒᵖ ⥤ Type d :=
    D.op ⋙ CategoryTheory.yoneda.obj T
  let R := (pointedCochainRepresentative C J p).obj K
  let e (Y : PointedSimplicialPresheaf.{w} C) (f : Y ⟶ R) :
      F.obj (op (Q.obj Y)) :=
    τ.hom.app Y ≫ pointedCochainRepresentativeDerivedMap C J p K Y f
  have hNat {Y Z : PointedSimplicialPresheaf.{w} C} (f : Y ⟶ Z) (g : Z ⟶ R) :
      e Y (f ≫ g) = F.map (Q.map f).op (e Z g) := by
    change τ.hom.app Y ≫ pointedCochainRepresentativeDerivedMap C J p K Y (f ≫ g) =
      D.map (Q.map f) ≫ τ.hom.app Z ≫ pointedCochainRepresentativeDerivedMap C J p K Z g
    rw [pointedCochainRepresentativeDerivedMap_precomp, reducedHypercohomology_map_apply]
    exact (τ.hom.naturality_assoc f _).symm
  have hSurj (Y : PointedSimplicialPresheaf.{w} C) : Function.Surjective (e Y) := by
    intro z
    let a : (reducedHypercohomology C J K p).obj (op Y) := τ.inv.app Y ≫ z
    obtain ⟨f, hf⟩ := pointedCochainRepresentativeDerivedMap_surjective C J p K Y a
    refine ⟨f, ?_⟩
    change τ.hom.app Y ≫ pointedCochainRepresentativeDerivedMap C J p K Y f = z
    rw [hf]
    exact (τ.app Y).hom_inv_id_assoc z
  have hEq (Y : PointedSimplicialPresheaf.{w} C) {f g : Y ⟶ R}
      (hf : e Y f = e Y g) : Q.map f = Q.map g := by
    change τ.hom.app Y ≫ pointedCochainRepresentativeDerivedMap C J p K Y f =
      τ.hom.app Y ≫ pointedCochainRepresentativeDerivedMap C J p K Y g at hf
    exact toStalkwiseHomotopyCategory_map_eq_of_derivedMap_eq C J p K Y f g
      ((cancel_epi (τ.hom.app Y)).mp hf)
  exact (Localization.homEquivOfStrictMaps Q (stalkwiseWeakEquivalences C J) F R
    e hNat hSurj hEq X).trans ((τ.app X).homCongr (Iso.refl T))

theorem stalkwiseCochainRepresentativeHomEquiv_apply
    (h : PointedSimplicialSetChainsPreserveRealizationWeakEquivalences.{w})
    (p : ℤ) (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) [K.IsKInjective]
    (X : PointedSimplicialPresheaf.{w} C)
    (a : (toStalkwiseHomotopyCategory C J).obj X ⟶
      (toStalkwiseHomotopyCategory C J).obj ((pointedCochainRepresentative C J p).obj K)) :
    stalkwiseCochainRepresentativeHomEquiv C J h p K X a =
      (stalkwiseReducedDerivedChainsFactors C J h).inv.app X ≫
        (stalkwiseReducedDerivedChains C J h).map a ≫
        (stalkwiseReducedDerivedChainsFactors C J h).hom.app
          ((pointedCochainRepresentative C J p).obj K) ≫
        pointedCochainRepresentativeDerivedMap C J p K
          ((pointedCochainRepresentative C J p).obj K) (𝟙 _) := by
  let τ := stalkwiseReducedDerivedChainsFactors C J h
  let D := stalkwiseReducedDerivedChains C J h
  let R := (pointedCochainRepresentative C J p).obj K
  let z := pointedCochainRepresentativeDerivedMap C J p K R (𝟙 R)
  change τ.inv.app X ≫ (D.map a ≫ τ.hom.app R ≫ z) ≫ 𝟙 _ =
    τ.inv.app X ≫ D.map a ≫ τ.hom.app R ≫ z
  rw [Category.comp_id]

theorem stalkwiseCochainRepresentativeHomEquiv_naturality
    (h : PointedSimplicialSetChainsPreserveRealizationWeakEquivalences.{w})
    (p : ℤ) (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) [K.IsKInjective]
    {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y)
    (a : (toStalkwiseHomotopyCategory C J).obj Y ⟶
      (toStalkwiseHomotopyCategory C J).obj ((pointedCochainRepresentative C J p).obj K)) :
    stalkwiseCochainRepresentativeHomEquiv C J h p K X
        ((toStalkwiseHomotopyCategory C J).map f ≫ a) =
      (reducedHypercohomology C J K p).map f.op
        (stalkwiseCochainRepresentativeHomEquiv C J h p K Y a) := by
  simp only [stalkwiseCochainRepresentativeHomEquiv_apply, Functor.map_comp, Category.assoc]
  exact ((stalkwiseReducedDerivedChainsFactors C J h).inv.naturality_assoc f _).symm

theorem stalkwiseCochainRepresentativeHomEquiv_map
    (h : PointedSimplicialSetChainsPreserveRealizationWeakEquivalences.{w})
    (p : ℤ) (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) [K.IsKInjective]
    (X : PointedSimplicialPresheaf.{w} C) (f : X ⟶ (pointedCochainRepresentative C J p).obj K) :
    stalkwiseCochainRepresentativeHomEquiv C J h p K X
        ((toStalkwiseHomotopyCategory C J).map f) =
      pointedCochainRepresentativeDerivedMap C J p K X f := by
  rw [stalkwiseCochainRepresentativeHomEquiv_apply]
  let τ := stalkwiseReducedDerivedChainsFactors C J h
  let D := stalkwiseReducedDerivedChains C J h
  let Q := toStalkwiseHomotopyCategory.{w} C J
  let R := (pointedCochainRepresentative C J p).obj K
  let z := pointedCochainRepresentativeDerivedMap C J p K R (𝟙 R)
  change τ.inv.app X ≫ D.map (Q.map f) ≫ τ.hom.app R ≫ z = _
  have hn : D.map (Q.map f) ≫ τ.hom.app R ≫ z =
      τ.hom.app X ≫ (reducedDerivedChains C J).map f ≫ z :=
    τ.hom.naturality_assoc f z
  rw [hn]
  refine ((τ.app X).inv_hom_id_assoc _).trans ?_
  have hf := pointedCochainRepresentativeDerivedMap_precomp C J p K f (𝟙 R)
  rw [Category.comp_id, reducedHypercohomology_map_apply] at hf
  exact hf.symm

attribute [colib_tag "COL-1014"]
  toStalkwiseHomotopyCategory_map_eq_of_derivedMap_eq
  stalkwiseCochainRepresentativeHomEquiv
  stalkwiseCochainRepresentativeHomEquiv_naturality
  stalkwiseCochainRepresentativeHomEquiv_map
attribute [colib_ref "Voevodsky2003ReducedPowers" "Section 2, equation (2.9), p. 5"
  "ingredient" "The reduced derived-Hom expression used in the stalkwise comparison"]
  stalkwiseCochainRepresentativeHomEquiv

end CategoryTheory.PointedSimplicialPresheaf
