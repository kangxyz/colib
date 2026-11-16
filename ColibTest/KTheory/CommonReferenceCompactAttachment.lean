module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceCompactAttachment

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Simplicial Topology unitInterval

universe u

namespace ColibTest.CommonReferenceCompactAttachment

variable {V W Z : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (J : W ⟶ Z) (G : V ⟶ Z)
  (ε : G.hom.toFunctor ≅ (F ≫ J).hom.toFunctor)

/-- Arbitrary reanchoring compares the entire joint family over the original cube. -/
theorem attach_whole_cube (p : C((Fin 3 → unitInterval), |nerve (Codiscrete (Node F))|))
    (n : ℕ) :
    compactPrespectrumFamily G ((attachPostcompParameter F J G ε).comp p) n =
      ((prespectrumMap J).map n).comp (compactPrespectrumFamily F p n) :=
  compactPrespectrumFamily_attachPostcomp_map F J G ε p n

/-- The entire original loop and its independent internal time are preserved. -/
theorem attach_loop_time (p : C((Fin 3 → unitInterval), |nerve (Codiscrete (Node F))|))
    (r s t z : unitInterval) (γ : Path (stagePoint 0 V) (stagePoint 0 V)) :
    (show Path (stagePoint 0 Z) (stagePoint 0 Z) from
      compactPrespectrumFamily G ((attachPostcompParameter F J G ε).comp p) 0
        (![r, s, t], γ)) z =
    (show Path (stagePoint 0 Z) (stagePoint 0 Z) from
      (prespectrumMap J).map 0 (compactPrespectrumFamily F p 0 (![r, s, t], γ))) z := by
  exact congrArg (fun a : Path (stagePoint 0 Z) (stagePoint 0 Z) ↦ a z)
    (compactPrespectrumFamily_attachPostcomp F J G ε p 0 ![r, s, t] γ)

end ColibTest.CommonReferenceCompactAttachment
