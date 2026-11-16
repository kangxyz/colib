module

public import Colib.Topology.Prespectrum.PushoutSquareFilling

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval

universe u

namespace ColibTest.PushoutSquareFilling

open HomotopyPushout

variable {A B C D : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {a₀₀ a₀₁ a₁₀ a₁₁ : prespectrum f g ⟶ D}
  (H₀ : Homotopy a₀₀ a₀₁) (H₁ : Homotopy a₁₀ a₁₁)
  (L : Homotopy a₀₀ a₁₀) (M : Homotopy a₀₁ a₁₁)
  (SL : (Homotopy.precomp (inl f g) H₀).Square (Homotopy.precomp (inl f g) H₁)
    (Homotopy.precomp (inl f g) L) (Homotopy.precomp (inl f g) M))
  (SR : (Homotopy.precomp (inr f g) H₀).Square (Homotopy.precomp (inr f g) H₁)
    (Homotopy.precomp (inr f g) L) (Homotopy.precomp (inr f g) M))
  (Q : SquareCylinder f g H₀ H₁ L M SL SR)

/-- Descent keeps every original overlap point at all three independent coordinates. -/
theorem whole_overlap (n : ℕ) (r s t : unitInterval) (x : A.space n) :
    (squareOfCylinder f g H₀ H₁ L M SL SR Q).level n (r, (s, cylinder f g n (t, x))) =
      Q.level n (r, (s, (t, x))) :=
  squareOfCylinder_cylinder f g H₀ H₁ L M SL SR Q n r s t x

/-- The prescribed left and right squares survive at all points of the original chart faces. -/
theorem original_charts (n : ℕ) (r s : unitInterval) (x : B.space n) (y : C.space n) :
    (squareOfCylinder f g H₀ H₁ L M SL SR Q).level n (r, (s, (inl f g).map n x)) =
      SL.level n (r, (s, x)) ∧
    (squareOfCylinder f g H₀ H₁ L M SL SR Q).level n (r, (s, (inr f g).map n y)) =
      SR.level n (r, (s, y)) :=
  ⟨squareOfCylinder_inl f g H₀ H₁ L M SL SR Q n r s x,
    squareOfCylinder_inr f g H₀ H₁ L M SL SR Q n r s y⟩

/-- The structure map has its own time even on the full overlap cylinder. -/
theorem overlap_structure_clock (n : ℕ) (r s t z : unitInterval) (x : A.space n) :
    (squareOfCylinder f g H₀ H₁ L M SL SR Q).level (n + 1)
      (r, (s, cylinder f g (n + 1) (t, A.structureMap n x z))) =
      D.structureMap n
        ((squareOfCylinder f g H₀ H₁ L M SL SR Q).level n
          (r, (s, cylinder f g n (t, x)))) z := by
  rw [squareOfCylinder_cylinder, squareOfCylinder_cylinder]
  exact Q.comm n r s t x z

end ColibTest.PushoutSquareFilling
