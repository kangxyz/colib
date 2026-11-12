/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Colib.CategoryTheory.Sites.Hypercohomology.FiniteWindow
public import Colib.CategoryTheory.Sites.Hypercohomology.RestrictionDevissage
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle

/-!
# Restriction on bounded-above representable hypercohomology

A common finite projective dimension bound `d` for two free representing
sheaves reduces degree-`p` restriction to the canonical truncation at
`p-d`. Bounded-above coefficients then give a finite interval of cohomology
sheaves, so invertibility of their ordinary restrictions suffices. The
comparison commutes with restriction by naturality of the actual truncation
map on the native derived Hom presheaf.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe g w w' t v u

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasExt.{w'} (Sheaf J AddCommGrpCat.{max v t})]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{max v t})]
  [IsGrothendieckAbelian.{g} (Sheaf J AddCommGrpCat.{max v t})]

/-- If both free representing sheaves have projective dimension at most
`d`, ordinary invariance of the cohomology sheaves of a bounded-above
derived object implies invariance of its derived Hom restriction. -/
theorem isIso_derivedHomPresheaf_map_of_isLE
    {X Y : C} (f : X ⟶ Y) (d : ℕ)
    [HasProjectiveDimensionLE ((freeYoneda.{t} J).obj X) d]
    [HasProjectiveDimensionLE ((freeYoneda.{t} J).obj Y) d]
    (E : DerivedCategory (Sheaf J AddCommGrpCat.{max v t})) (b : ℤ) (hE : E.IsLE b)
    (h : ∀ (q : ℤ) (m : ℕ), IsIso ((cohomologyPresheaf.{w', t}
      ((DerivedCategory.homologyFunctor _ q).obj E) m).map f.op)) (p : ℤ) :
    IsIso (((derivedHomPresheafFunctor.{w, t} J p).obj E).map f.op) := by
  let a : ℤ := p - (d : ℤ)
  let B := max b a
  let L := (DerivedCategory.TStructure.t.truncGE a).obj E
  let π : E ⟶ L := (DerivedCategory.TStructure.t.truncGEπ a).app E
  have hGE : L.IsGE a :=
    inferInstanceAs (((DerivedCategory.TStructure.t.truncGE a).obj E).IsGE a)
  have hLE : L.IsLE B := (DerivedCategory.isLE_iff L B).mpr (fun q hq ↦ by
    let : IsIso ((DerivedCategory.homologyFunctor _ q).map π) :=
      DerivedCategory.isIso_homologyMap_truncGEπ_app a q (by dsimp [B] at hq; omega) E
    exact (asIso ((DerivedCategory.homologyFunctor _ q).map π)).isZero_iff.mp
      ((DerivedCategory.isLE_iff E b).mp hE q (by dsimp [B] at hq; omega)))
  have hB : a + ((B - a).toNat : ℤ) = B := by dsimp [B]; omega
  let F := derivedHomPresheafFunctor.{w, t} J p
  let : IsIso ((F.obj L).map f.op) :=
    isIso_derivedHomPresheaf_map_of_bounded J f L a (B - a).toNat hGE
      (by simpa only [hB] using hLE) (fun q hq _ m ↦ by
        let : IsIso ((DerivedCategory.homologyFunctor _ q).map π) :=
          DerivedCategory.isIso_homologyMap_truncGEπ_app a q hq E
        let e := (cohomologyPresheafFunctor.{w', t} J m).mapIso
          (asIso ((DerivedCategory.homologyFunctor _ q).map π))
        exact (NatIso.isIso_map_iff e f.op).mp (h q m)) p
  let η : F.obj E ⟶ F.obj L := F.map π
  let : IsIso (η.app (op X)) := (ConcreteCategory.isIso_iff_bijective _).mpr
    (DerivedCategory.bijective_comp_truncGEπ_of_hasProjectiveDimensionLE
      ((freeYoneda.{t} J).obj X) d E p)
  let : IsIso (η.app (op Y)) := (ConcreteCategory.isIso_iff_bijective _).mpr
    (DerivedCategory.bijective_comp_truncGEπ_of_hasProjectiveDimensionLE
      ((freeYoneda.{t} J).obj Y) d E p)
  have : IsIso ((F.obj E).map f.op ≫ η.app (op X)) := by
    rw [η.naturality f.op]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (η.app (op X))

/-- The derived cutoff applies to the original hypercohomology presheaf of
a cochain complex bounded above in cohomology. -/
theorem isIso_hypercohomologyPresheaf_map_of_isLE
    {X Y : C} (f : X ⟶ Y) (d : ℕ)
    [HasProjectiveDimensionLE ((freeYoneda.{t} J).obj X) d]
    [HasProjectiveDimensionLE ((freeYoneda.{t} J).obj Y) d]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{max v t}) ℤ) (b : ℤ) (hK : K.IsLE b)
    (h : ∀ (q : ℤ) (m : ℕ), IsIso ((cohomologyPresheaf.{w', t} (K.homology q) m).map f.op))
    (p : ℤ) :
    IsIso ((hypercohomologyPresheaf.{w, t} J K p).map f.op) := by
  apply isIso_derivedHomPresheaf_map_of_isLE J f d (DerivedCategory.Q.obj K) b
    ((DerivedCategory.isLE_Q_obj_iff K b).mpr hK) ?_ p
  intro q m
  let e := (cohomologyPresheafFunctor.{w', t} J m).mapIso
    ((DerivedCategory.homologyFunctorFactors _ q).app K)
  exact (NatIso.isIso_map_iff e f.op).mpr (h q m)

end Stacks.Cohomology.FreeYonedaUnivLE
