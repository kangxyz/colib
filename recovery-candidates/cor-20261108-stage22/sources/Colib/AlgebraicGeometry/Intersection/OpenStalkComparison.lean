/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Length
public import StacksFrontier.Homology.Tor.Independence

/-!
# Stalk Tor under actual open squares

Recovery reconstruction, 2026-11-08. This is newly reconstructed source, not the original
historically checked byte sequence. It requires fresh elaboration and source review.

The comparison uses the actual structure-sheaf stalk maps of three open immersions.
No comparison, finite-length assumption, reducedness assumption, or replacement stalk
model is supplied. Point equalities remain part of the literal scalar actions.

Native sources: Mathlib `Scheme.Hom.stalkMap_comp`, `stalkMap_congr_hom`,
`ModuleCat.restrictScalarsIsoOfEquiv`, `restrictScalarsComp'App`; Stacks
`RingTheory.TorIndependence.torRestrictIso`. Mathematical background: Stacks,
Tags 0098 and 0660. The comparison itself is an application of these native results.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y X' Y' : Scheme.{u}}

/-- The stalk square of actual morphisms, retaining both ambient point equalities. -/
theorem Hom.stalkMap_square_of_eq
    (i : Y ⟶ X) (i' : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
    (h : b ≫ i = i' ≫ a) (x' : X') (y' : Y')
    (h' : x' = i' y') (hx : a x' = i (b y')) :
    ((X.presheaf.stalkCongr (.of_eq hx)).hom ≫ i.stalkMap (b y')) ≫
      b.stalkMap y' =
    a.stalkMap x' ≫ ((X'.presheaf.stalkCongr (.of_eq h')).hom ≫
      i'.stalkMap y') := by
  subst x'
  simpa only [Hom.stalkMap_comp, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp, Category.assoc] using
    (Hom.stalkMap_congr_hom (i' ≫ a) (b ≫ i) h.symm y').symm

/-- The actual source stalk module in an open square, restricted to the original ambient
stalk, is unchanged. All scalar actions are literal native stalk maps. -/
def stalkModuleIsoOfOpenSquare
    (i : Y ⟶ X) (i' : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
    [IsOpenImmersion a] [IsOpenImmersion b]
    (h : b ≫ i = i' ≫ a) (x' : X') (y' : Y')
    (h' : x' = i' y') (hx : a x' = i (b y')) :
    (ModuleCat.restrictScalars
      ((X.presheaf.stalkCongr (.of_eq hx)).hom ≫ i.stalkMap (b y')).hom).obj
      (ModuleCat.of (Y.presheaf.stalk (b y')) (Y.presheaf.stalk (b y'))) ≅
    (ModuleCat.restrictScalars (a.stalkMap x').hom).obj
      ((ModuleCat.restrictScalars
        ((X'.presheaf.stalkCongr (.of_eq h')).hom ≫ i'.stalkMap y').hom).obj
        (ModuleCat.of (Y'.presheaf.stalk y') (Y'.presheaf.stalk y'))) := by
  let f := ((X.presheaf.stalkCongr (.of_eq hx)).hom ≫ i.stalkMap (b y')).hom
  let g := ((X'.presheaf.stalkCongr (.of_eq h')).hom ≫ i'.stalkMap y').hom
  let eb := (asIso (b.stalkMap y')).commRingCatIsoToRingEquiv
  exact (ModuleCat.restrictScalars f).mapIso
      (ModuleCat.restrictScalarsIsoOfEquiv eb).symm ≪≫
    (ModuleCat.restrictScalarsComp'App f (b.stalkMap y').hom
      ((a.stalkMap x') ≫ (X'.presheaf.stalkCongr (.of_eq h')).hom ≫
        i'.stalkMap y').hom
      (congrArg CommRingCat.Hom.hom (Hom.stalkMap_square_of_eq i i' a b h x' y' h' hx).symm)
      _).symm ≪≫
    ModuleCat.restrictScalarsComp'App (a.stalkMap x').hom g _ rfl _

variable {Z Z' : Scheme.{u}}

/-- Tor of two actual stalk modules is invariant under a pair of actual open squares. -/
def torStalksIsoOfOpenSquares
    (i : Y ⟶ X) (j : Z ⟶ X) (i' : Y' ⟶ X') (j' : Z' ⟶ X')
    (a : X' ⟶ X) (b : Y' ⟶ Y) (c : Z' ⟶ Z)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c]
    (hi : b ≫ i = i' ≫ a) (hj : c ≫ j = j' ≫ a)
    (x' : X') (y' : Y') (z' : Z')
    (hy' : x' = i' y') (hz' : x' = j' z')
    (hy : a x' = i (b y')) (hz : a x' = j (c z')) (n : ℕ) :
    (((Tor (ModuleCat (X.presheaf.stalk (a x'))) n).obj
      ((ModuleCat.restrictScalars
        ((X.presheaf.stalkCongr (.of_eq hy)).hom ≫ i.stalkMap (b y')).hom).obj
        (ModuleCat.of (Y.presheaf.stalk (b y')) (Y.presheaf.stalk (b y'))))).obj
      ((ModuleCat.restrictScalars
        ((X.presheaf.stalkCongr (.of_eq hz)).hom ≫ j.stalkMap (c z')).hom).obj
        (ModuleCat.of (Z.presheaf.stalk (c z')) (Z.presheaf.stalk (c z'))))) ≅
    (ModuleCat.restrictScalars (a.stalkMap x').hom).obj
      ((((Tor (ModuleCat (X'.presheaf.stalk x')) n).obj
        ((ModuleCat.restrictScalars
          ((X'.presheaf.stalkCongr (.of_eq hy')).hom ≫ i'.stalkMap y').hom).obj
          (ModuleCat.of (Y'.presheaf.stalk y') (Y'.presheaf.stalk y'))))).obj
        ((ModuleCat.restrictScalars
          ((X'.presheaf.stalkCongr (.of_eq hz')).hom ≫ j'.stalkMap z').hom).obj
          (ModuleCat.of (Z'.presheaf.stalk z') (Z'.presheaf.stalk z')))) := by
  let ei := stalkModuleIsoOfOpenSquare i i' a b hi x' y' hy' hy
  let ej := stalkModuleIsoOfOpenSquare j j' a c hj x' z' hz' hz
  let ea := (asIso (a.stalkMap x')).commRingCatIsoToRingEquiv
  exact (((Tor (ModuleCat (X.presheaf.stalk (a x'))) n).mapIso ei).app _) ≪≫
    ((Tor (ModuleCat (X.presheaf.stalk (a x'))) n).obj _).mapIso ej ≪≫
    RingTheory.TorIndependence.torRestrictIso ea _ _ n

/-- The lengths of the actual Tor stalks agree, including infinite lengths. -/
theorem length_torStalks_eq_of_openSquares
    (i : Y ⟶ X) (j : Z ⟶ X) (i' : Y' ⟶ X') (j' : Z' ⟶ X')
    (a : X' ⟶ X) (b : Y' ⟶ Y) (c : Z' ⟶ Z)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c]
    (hi : b ≫ i = i' ≫ a) (hj : c ≫ j = j' ≫ a)
    (x' : X') (y' : Y') (z' : Z')
    (hy' : x' = i' y') (hz' : x' = j' z')
    (hy : a x' = i (b y')) (hz : a x' = j (c z')) (n : ℕ) :
    Module.length (X.presheaf.stalk (a x'))
      ((((Tor (ModuleCat (X.presheaf.stalk (a x'))) n).obj
        ((ModuleCat.restrictScalars
          ((X.presheaf.stalkCongr (.of_eq hy)).hom ≫ i.stalkMap (b y')).hom).obj
          (ModuleCat.of (Y.presheaf.stalk (b y')) (Y.presheaf.stalk (b y'))))).obj
        ((ModuleCat.restrictScalars
          ((X.presheaf.stalkCongr (.of_eq hz)).hom ≫ j.stalkMap (c z')).hom).obj
          (ModuleCat.of (Z.presheaf.stalk (c z')) (Z.presheaf.stalk (c z')))))) =
    Module.length (X'.presheaf.stalk x')
      ((((Tor (ModuleCat (X'.presheaf.stalk x')) n).obj
        ((ModuleCat.restrictScalars
          ((X'.presheaf.stalkCongr (.of_eq hy')).hom ≫ i'.stalkMap y').hom).obj
          (ModuleCat.of (Y'.presheaf.stalk y') (Y'.presheaf.stalk y'))))).obj
        ((ModuleCat.restrictScalars
          ((X'.presheaf.stalkCongr (.of_eq hz')).hom ≫ j'.stalkMap z').hom).obj
          (ModuleCat.of (Z'.presheaf.stalk z') (Z'.presheaf.stalk z')))) := by
  let e := torStalksIsoOfOpenSquares i j i' j' a b c hi hj x' y' z'
    hy' hz' hy hz n
  let ea := (asIso (a.stalkMap x')).commRingCatIsoToRingEquiv
  let := (a.stalkMap x').hom.toAlgebra
  let N := (((Tor (ModuleCat (X'.presheaf.stalk x')) n).obj
    ((ModuleCat.restrictScalars
      ((X'.presheaf.stalkCongr (.of_eq hy')).hom ≫ i'.stalkMap y').hom).obj
      (ModuleCat.of (Y'.presheaf.stalk y') (Y'.presheaf.stalk y'))))).obj
    ((ModuleCat.restrictScalars
      ((X'.presheaf.stalkCongr (.of_eq hz')).hom ≫ j'.stalkMap z').hom).obj
      (ModuleCat.of (Z'.presheaf.stalk z') (Z'.presheaf.stalk z')))
  let : IsScalarTower (X.presheaf.stalk (a x')) (X'.presheaf.stalk x')
      ((ModuleCat.restrictScalars (a.stalkMap x').hom).obj N) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact e.toLinearEquiv.length_eq.trans (Module.length_eq_of_surjective ea.surjective)

end AlgebraicGeometry.Scheme
