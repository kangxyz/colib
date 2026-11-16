module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceCompactPrespectrum

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Simplicial Topology unitInterval

universe u

namespace ColibTest.CommonReferenceCompactPrespectrum

variable {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)

/-- Cube carrier coordinates and the original independent structure time agree at any level. -/
theorem cube_structure (p : C((Fin 3 → unitInterval), |nerve (Codiscrete (Node F))|))
    (n : ℕ) (r s t z : unitInterval) (x : (prespectrum V).space n) :
    compactPrespectrumFamily F p (n + 1) (![r, s, t], (prespectrum V).structureMap n x z) =
      (prespectrum W).structureMap n (compactPrespectrumFamily F p n (![r, s, t], x)) z :=
  compactPrespectrumFamily_structure F p n _ x z

/-- Matching an actual face keeps the same evaluated level, including the loop level. -/
theorem cube_face (p : C((Fin 3 → unitInterval), |nerve (Codiscrete (Node F))|))
    (q : C(unitInterval × unitInterval, |nerve (Codiscrete (Node F))|))
    (n : ℕ) (s t : unitInterval) (h : p ![1, s, t] = q (s, t))
    (x : (prespectrum V).space n) :
    compactPrespectrumFamily F p n (![1, s, t], x) =
      compactPrespectrumFamily F q n ((s, t), x) :=
  compactPrespectrumFamily_of_point_eq F n p q _ _ h x

end ColibTest.CommonReferenceCompactPrespectrum
