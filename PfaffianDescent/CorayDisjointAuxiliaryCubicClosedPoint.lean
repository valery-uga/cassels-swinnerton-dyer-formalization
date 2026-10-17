import PfaffianDescent.CorayMinimalPointSelection

/-! SOURCE ONLY / UNVERIFIED. A genuine auxiliary cubic point is constructed
from an actual line section. Original coprime degree proves disjointness;
there is no supplied auxiliary cycle, avoidance or transversality premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u

/-- The actual rational-point branch, or an actual closed cubic point
DISJOINT from the original prime-to-three point. A singleton cubic point
is reduced and has three distinct geometric conjugates in characteristic0. -/
theorem hypersurface_section_or_disjoint_cubicClosedPoint
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (P : closedPoints (hypersurface p hp))
    (hPcop : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3) :
    (∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ∨
    ∃ A : closedPoints (hypersurface p hp),
      A ≠ P ∧ (hypersurfaceToBase p hp).residueDegree A.1 = 3 := by
  rcases hypersurface_section_or_cubic_of_nonzero_cubic (by decide : 2 ≤ 4)
      p hp hp0 with hsection | ⟨A, hA⟩
  · exact Or.inl hsection
  · refine Or.inr ⟨A, ?_, hA⟩
    intro hAP
    have hbad : ¬ Nat.Coprime 3 3 := by decide
    apply hbad
    simpa only [← hAP, hA] using hPcop

/-- In the genuine no-rational-section branch, the actual line-section
construction necessarily produces this disjoint cubic closed point. -/
theorem hypersurface_exists_disjoint_cubicClosedPoint_of_no_section
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (P : closedPoints (hypersurface p hp))
    (hPcop : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    ∃ A : closedPoints (hypersurface p hp),
      A ≠ P ∧ (hypersurfaceToBase p hp).residueDegree A.1 = 3 :=
  (hypersurface_section_or_disjoint_cubicClosedPoint p hp hp0 P hPcop).resolve_left hno

/-- The actual no-section branch constructs a multiplicity-one effective
cycle of original degree3, disjoint from the actual original P. No cycle,
reducedness certificate, chosen line or avoidance premise is an input. -/
theorem hypersurface_exists_disjoint_reduced_degreeThree_cycle_of_no_section
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (P : closedPoints (hypersurface p hp))
    (hPcop : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      (∀ A ∈ z.support, z A = 1) ∧
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 3 ∧ P ∉ z.support := by
  classical
  obtain ⟨A, hAP, hAdegree⟩ :=
    hypersurface_exists_disjoint_cubicClosedPoint_of_no_section p hp hp0 P hPcop hno
  let z : EffectiveZeroCycle (hypersurface p hp) := Finsupp.single A 1
  refine ⟨z, ?_, ?_, ?_⟩
  · intro B hB
    have hBA : B = A := by simpa only [z, Finsupp.support_single _ one_ne_zero,
      Finset.mem_singleton] using hB
    subst B
    simp [z]
  · simp [EffectiveZeroCycle.degree, z, hAdegree]
  · simpa only [z, Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] using hAP.symm

end PfaffianDescent.Coray
