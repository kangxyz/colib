/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.Sites.Smooth.FiniteProducts
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# The augmented Čech nerve of a smooth scheme

The terms are the finite relative powers of the smooth scheme. A simplex
operator acts by precomposition on the coordinate projections, as in
Voevodsky, *Motivic cohomology with Z/2-coefficients*, Definition 9.1.
The augmentation targets the actual base scheme and any section gives
Mathlib's extra degeneracy of the split Čech nerve.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}}

/-- The native terminal Čech nerve formed by finite relative powers of `X`. -/
abbrev cechNerve (X : SmoothSite S) : SimplicialObject (SmoothSite S) :=
  CategoryTheory.cechNerveTerminalFrom X

/-- The augmented Čech nerve with the identity scheme as its augmentation target. -/
def augmentedCechNerve (X : SmoothSite S) : SimplicialObject.Augmented (SmoothSite S) :=
  (cechNerve X).augmentOfIsTerminal (baseIsTerminal S)

/-- The structural augmentation from the Čech nerve to the constant base scheme. -/
abbrev cechAugmentation (X : SmoothSite S) :
    cechNerve X ⟶ (SimplicialObject.const (SmoothSite S)).obj (base S) :=
  (augmentedCechNerve X).hom

/-- The coordinate of a relative power in the Čech nerve. -/
def cechProjection (X : SmoothSite S) (n : SimplexCategory) (i : Fin (n.len + 1)) :
    (cechNerve X).obj (op n) ⟶ X :=
  Pi.π (fun _ : Fin (n.len + 1) => X) i

@[reassoc (attr := simp)]
theorem cechNerve_map_cechProjection (X : SmoothSite S) {m n : SimplexCategory}
    (f : m ⟶ n) (i : Fin (m.len + 1)) :
    (cechNerve X).map f.op ≫ cechProjection X m i =
      cechProjection X n (f.toOrderHom i) :=
  Pi.lift_comp_π _ _

/-- A map into a Čech term is a tuple of maps into the original smooth scheme. -/
def cechHomEquiv (U X : SmoothSite S) (n : SimplexCategory) :
    (U ⟶ (cechNerve X).obj (op n)) ≃ (Fin (n.len + 1) → (U ⟶ X)) where
  toFun f i := f ≫ cechProjection X n i
  invFun f := Pi.lift f
  left_inv f := by
    apply Pi.hom_ext
    intro i
    exact Pi.lift_comp_π _ _
  right_inv f := funext fun i => Pi.lift_comp_π _ _

/-- Functoriality of the Čech nerve by applying a morphism to every coordinate. -/
def cechNerveFunctor (S : Scheme.{u}) : SmoothSite S ⥤ SimplicialObject (SmoothSite S) where
  obj := cechNerve
  map f :=
    { app := fun n => Limits.Pi.map (fun _ : Fin (n.unop.len + 1) => f)
      naturality := by
        intro m n g
        apply Pi.hom_ext
        intro i
        simp [cechNerve, cechNerveTerminalFrom, Category.assoc] }
  map_id X := by
    ext n : 1
    exact Limits.Pi.map_id
  map_comp f g := by
    ext n : 1
    exact (Limits.Pi.map_comp_map (fun _ : Fin (n.unop.len + 1) => f) (fun _ => g)).symm

/-- A map of smooth schemes induces a map of their Čech nerves. -/
abbrev cechNerveMap {X Y : SmoothSite S} (f : X ⟶ Y) : cechNerve X ⟶ cechNerve Y :=
  (cechNerveFunctor S).map f

@[reassoc (attr := simp)]
theorem cechNerveMap_app_cechProjection {X Y : SmoothSite S} (f : X ⟶ Y)
    (n : SimplexCategory) (i : Fin (n.len + 1)) :
    (cechNerveMap f).app (op n) ≫ cechProjection Y n i = cechProjection X n i ≫ f := by
  change Limits.Pi.map (fun _ : Fin (n.len + 1) => f) ≫ Pi.π (fun _ => Y) i =
    Pi.π (fun _ => X) i ≫ f
  exact Limits.Pi.map_π _ _

@[reassoc (attr := simp)]
theorem cechNerveMap_comp_cechAugmentation {X Y : SmoothSite S} (f : X ⟶ Y) :
    cechNerveMap f ≫ cechAugmentation Y = cechAugmentation X := by
  ext n : 1
  exact (baseIsTerminal S).hom_ext _ _

/-- The product Čech nerve identifies with the native augmented arrow Čech nerve. -/
def augmentedCechNerveIso (X : SmoothSite S) :
    (Arrow.mk (terminal.from X)).augmentedCechNerve ≅ augmentedCechNerve X :=
  Comma.isoMk (CechNerveTerminalFrom.iso X)
    (terminalIsTerminal.uniqueUpToIso (baseIsTerminal S)) (by
      ext n : 1
      exact (baseIsTerminal S).hom_ext _ _)

/-- A section of the structure map gives an extra degeneracy of the augmented Čech nerve. -/
def cechExtraDegeneracy {X : SmoothSite S} (s : base S ⟶ X) :
    SimplicialObject.Augmented.ExtraDegeneracy (augmentedCechNerve X) := by
  let e := augmentedCechNerveIso X
  let split : SplitEpi (terminal.from X) :=
    ⟨e.hom.right ≫ s, terminal.hom_ext _ _⟩
  exact SimplicialObject.Augmented.ExtraDegeneracy.ofIso e
    (Arrow.AugmentedCechNerve.extraDegeneracy (Arrow.mk (terminal.from X)) split)

end AlgebraicGeometry.Scheme.SmoothSite

attribute [colib_tag "COL-0384"]
  AlgebraicGeometry.Scheme.SmoothSite.cechNerveFunctor
  AlgebraicGeometry.Scheme.SmoothSite.cechAugmentation
  AlgebraicGeometry.Scheme.SmoothSite.cechExtraDegeneracy
attribute [colib_ref "Voevodsky2003ModTwo" "Appendix B, Definition 9.1, p. 102" "adaptation"
  "The actual augmented Cech nerve, generalized to a smooth site over an arbitrary scheme"]
  AlgebraicGeometry.Scheme.SmoothSite.cechNerveFunctor
