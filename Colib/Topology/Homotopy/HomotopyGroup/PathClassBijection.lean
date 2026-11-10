/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Homotopy.HomotopyGroup.FundamentalGroup

/-!
# The original first homotopy map controls every based path-class fiber

A path from the basepoint to the other source endpoint identifies that path
fiber with the loop torsor. Bijectivity is transported through actual groupoid
composition. The comparison with the original cubical Pi one map uses its
proved naturality, rather than assuming fullness of a fundamental groupoid.
-/

@[expose] public section
noncomputable section
open CategoryTheory
universe u v u₁ v₁

namespace HomotopyGroup

private theorem groupoid_hom_bijective_of_end_bijective
    {C : Type u} {D : Type v} [Groupoid.{u₁} C] [Groupoid.{v₁} D]
    (F : C ⥤ D) (b x : C) (p : b ⟶ x)
    (hF : Function.Bijective (fun q : b ⟶ b ↦ F.map q)) :
    Function.Bijective (fun q : b ⟶ x ↦ F.map q) := by
  constructor
  · intro q r hqr
    apply (cancel_mono (inv p)).mp
    apply hF.injective
    simpa only [F.map_comp] using congrArg (fun t ↦ t ≫ F.map (inv p)) hqr
  · intro q
    obtain ⟨r, hr⟩ := hF.surjective (q ≫ inv (F.map p))
    refine ⟨r ≫ p, ?_⟩
    change F.map r = _ at hr
    change F.map (r ≫ p) = q
    rw [F.map_comp, hr]
    simp

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Bijectivity of the original Pi one map implies bijectivity of the actual
loop-class map, through the established natural comparison of the two models. -/
theorem fundamentalGroupMap_bijective_of_piMap (f : C(X, Y)) (b : X)
    (hf : Function.Bijective (piMap 0 f (x := b) rfl)) :
    Function.Bijective (FundamentalGroup.map f b) := by
  let eX := HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := b)
  let eY := HomotopyGroup.pi1MulEquivFundamentalGroup (X := Y) (x := f b)
  have hcomm : eY ∘ piMap 0 f (x := b) rfl = FundamentalGroup.map f b ∘ eX := by
    funext a
    change HomotopyGroup.pi1MulEquivFundamentalGroup (HomotopyGroup.map f rfl a) =
      End.of ((HomotopyGroup.pi1MulEquivFundamentalGroup a).asHom.map f)
    simpa only [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl] using
      HomotopyGroup.pi1MulEquivFundamentalGroup_naturality f rfl a
  have h := eY.bijective.comp hf
  rw [hcomm] at h
  exact (Function.Bijective.of_comp_iff (FundamentalGroup.map f b) eX.bijective).mp h

/-- One actual connecting path suffices to identify the original based
path-class map as a bijection from bijectivity on actual loop classes. -/
theorem pathClassMap_bijective_of_fundamentalGroupMap (f : C(X, Y)) (b x : X)
    (p : Path b x) (hf : Function.Bijective (FundamentalGroup.map f b)) :
    Function.Bijective (fun q : Path.Homotopic.Quotient b x ↦ q.map f) := by
  exact groupoid_hom_bijective_of_end_bijective (FundamentalGroupoid.map f)
    (FundamentalGroupoid.mk b) (FundamentalGroupoid.mk x) (.mk p) (by
      constructor
      · intro q r h
        have e := hf.injective (show FundamentalGroup.map f b (End.of q) =
          FundamentalGroup.map f b (End.of r) from congrArg End.of h)
        exact congrArg End.asHom e
      · intro q
        obtain ⟨r, hr⟩ := hf.surjective (End.of q)
        exact ⟨r.asHom, congrArg End.asHom hr⟩)

/-- On a path-connected source, the original Pi one isomorphism makes every
regular basis path-class map bijective. No target connectivity is needed here. -/
theorem pathClassMap_bijective_of_piMap [PathConnectedSpace X] (f : C(X, Y)) (b x : X)
    (hf : Function.Bijective (piMap 0 f (x := b) rfl)) :
    Function.Bijective (fun q : Path.Homotopic.Quotient b x ↦ q.map f) :=
  pathClassMap_bijective_of_fundamentalGroupMap f b x (PathConnectedSpace.somePath b x)
    (fundamentalGroupMap_bijective_of_piMap f b hf)

/-- The resulting equivalence still sends a class to its actual image under f. -/
def pathClassMapEquiv [PathConnectedSpace X] (f : C(X, Y)) (b x : X)
    (hf : Function.Bijective (piMap 0 f (x := b) rfl)) :
    Path.Homotopic.Quotient b x ≃ Path.Homotopic.Quotient (f b) (f x) :=
  Equiv.ofBijective (fun q ↦ q.map f) (pathClassMap_bijective_of_piMap f b x hf)

@[simp] theorem pathClassMapEquiv_apply [PathConnectedSpace X] (f : C(X, Y)) (b x : X)
    (hf : Function.Bijective (piMap 0 f (x := b) rfl))
    (q : Path.Homotopic.Quotient b x) : pathClassMapEquiv f b x hf q = q.map f := rfl

attribute [colib_ref "quillen"
  "Quillen/Topology/HomotopyGroups/PathClassBijection.lean:51-63"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  fundamentalGroupMap_bijective_of_piMap

attribute [colib_ref "quillen"
  "Quillen/Topology/HomotopyGroups/PathClassBijection.lean:67-71"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  pathClassMap_bijective_of_fundamentalGroupMap

attribute [colib_ref "quillen"
  "Quillen/Topology/HomotopyGroups/PathClassBijection.lean:75-79"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  pathClassMap_bijective_of_piMap

attribute [colib_ref "quillen"
  "Quillen/Topology/HomotopyGroups/PathClassBijection.lean:82-85"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  pathClassMapEquiv

attribute [colib_ref "quillen"
  "Quillen/Topology/HomotopyGroups/PathClassBijection.lean:87-89"
  "adaptation" "Actual regular coefficients, generators and the original map"]
  pathClassMapEquiv_apply

attribute [colib_tag "COL-0520"] pathClassMap_bijective_of_piMap

end HomotopyGroup
