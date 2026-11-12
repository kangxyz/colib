/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.NormalComponents
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# The normal component containing sections over a local base

The actual irreducible component through a point of a normal locally Noetherian scheme is
clopen. A morphism from the spectrum of a local ring lands in this open component as soon as
its closed point does. In particular, two original sections with the same specialization
factor through one actual integral component. Neither integrality of the whole scheme nor a
smooth finite-type presentation of the local base is assumed.

The component is the native `irreducibleComponent`, not a supplied component or decomposition.
The construction uses the clopen consequence of Stacks Project, Tag 0357, and the native
`Scheme.preimage_eq_top_of_closedPoint_mem` local-spectrum lemma.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-- The actual clopen irreducible component through a point, as an open subscheme. -/
def normalComponentOpen (x : X) : X.Opens :=
  ⟨irreducibleComponent x, (isClopen_of_mem_irreducibleComponents_of_isNormal _
    (irreducibleComponent_mem_irreducibleComponents x)).isOpen⟩

/-- The chosen open has exactly the points of the native irreducible component. -/
@[simp] theorem coe_normalComponentOpen (x : X) :
    (normalComponentOpen x : Set X) = irreducibleComponent x := rfl

/-- The actual component is also closed. -/
theorem isClopen_normalComponentOpen (x : X) :
    IsClopen (normalComponentOpen x : Set X) :=
  isClopen_of_mem_irreducibleComponents_of_isNormal _
    (irreducibleComponent_mem_irreducibleComponents x)

/-- The point lies in its actual component. -/
theorem mem_normalComponentOpen (x : X) : x ∈ normalComponentOpen x :=
  mem_irreducibleComponent

/-- The component is an integral scheme even when the ambient scheme is disconnected. -/
instance isIntegral_normalComponentOpen (x : X) :
    IsIntegral (normalComponentOpen x).toScheme := by
  let : IrreducibleSpace (normalComponentOpen x).toScheme :=
    Subtype.irreducibleSpace (irreducibleComponent_mem_irreducibleComponents x).1
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The component inclusion is a closed immersion as well as an open immersion. -/
instance isClosedImmersion_normalComponentOpen (x : X) :
    IsClosedImmersion (normalComponentOpen x).ι := by
  apply IsClosedImmersion.of_isPreimmersion
  rw [Opens.range_ι]
  exact (isClopen_normalComponentOpen x).isClosed

variable {R : CommRingCat.{u}} [IsLocalRing R]

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- A local-spectrum map whose closed point lands in an open has its entire image there. -/
theorem range_subset_open_of_closedPoint_mem (s : Spec R ⟶ X) (U : X.Opens)
    (hs : s (IsLocalRing.closedPoint R) ∈ U) : Set.range s ⊆ Set.range U.ι := by
  rw [Opens.range_ι]
  rintro _ ⟨r, rfl⟩
  exact (preimage_eq_top_of_closedPoint_mem s hs).ge (show r ∈ (⊤ : (Spec R).Opens) from trivial)

/-- Factor an original local-spectrum map through the component of its closed-point image. -/
def liftToNormalComponent (s : Spec R ⟶ X) (x : X)
    (hs : s (IsLocalRing.closedPoint R) ∈ normalComponentOpen x) :
    Spec R ⟶ (normalComponentOpen x).toScheme :=
  IsOpenImmersion.lift (normalComponentOpen x).ι s
    (range_subset_open_of_closedPoint_mem s _ hs)

/-- The lift retains the original morphism, rather than only its closed-point value. -/
@[reassoc (attr := simp)] theorem liftToNormalComponent_ι (s : Spec R ⟶ X) (x : X)
    (hs : s (IsLocalRing.closedPoint R) ∈ normalComponentOpen x) :
    liftToNormalComponent s x hs ≫ (normalComponentOpen x).ι = s :=
  IsOpenImmersion.lift_fac _ _ _

/-- Equality after any specialization of the two original maps is preserved by their lifts.
This retains equality of morphisms, not only equality of their underlying points. -/
theorem comp_liftToNormalComponent_eq_of_comp_eq
    {T : Scheme.{u}} (g : T ⟶ Spec R) (s₀ s₁ : Spec R ⟶ X) (x : X)
    (h₀ : s₀ (IsLocalRing.closedPoint R) ∈ normalComponentOpen x)
    (h₁ : s₁ (IsLocalRing.closedPoint R) ∈ normalComponentOpen x)
    (hs : g ≫ s₀ = g ≫ s₁) :
    g ≫ liftToNormalComponent s₀ x h₀ = g ≫ liftToNormalComponent s₁ x h₁ := by
  apply (cancel_mono (normalComponentOpen x).ι).mp
  simpa only [Category.assoc, liftToNormalComponent_ι] using hs

/-- Two maps from the same local spectrum with equal closed-point images factor through
one actual clopen integral component. Both original morphisms are retained exactly. -/
theorem exists_integral_component_lifts_of_closedPoint_eq
    (s₀ s₁ : Spec R ⟶ X)
    (hs : s₀ (IsLocalRing.closedPoint R) = s₁ (IsLocalRing.closedPoint R)) :
    ∃ (U : X.Opens) (t₀ t₁ : Spec R ⟶ U.toScheme),
      (U : Set X) = irreducibleComponent (s₀ (IsLocalRing.closedPoint R)) ∧
      IsClopen (U : Set X) ∧ IsIntegral U.toScheme ∧ IsClosedImmersion U.ι ∧
      t₀ ≫ U.ι = s₀ ∧ t₁ ≫ U.ι = s₁ := by
  let x := s₀ (IsLocalRing.closedPoint R)
  have h₀ : s₀ (IsLocalRing.closedPoint R) ∈ normalComponentOpen x :=
    mem_normalComponentOpen x
  have h₁ : s₁ (IsLocalRing.closedPoint R) ∈ normalComponentOpen x := hs ▸ h₀
  exact ⟨normalComponentOpen x, liftToNormalComponent s₀ x h₀,
    liftToNormalComponent s₁ x h₁, rfl, isClopen_normalComponentOpen x,
    inferInstance, inferInstance, liftToNormalComponent_ι _ _ _, liftToNormalComponent_ι _ _ _⟩

end AlgebraicGeometry.Scheme
