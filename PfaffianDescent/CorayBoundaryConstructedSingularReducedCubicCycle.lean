import PfaffianDescent.CorayBoundarySelectedCurveOriginalPointsCycle
import PfaffianDescent.CoraySelectedCurveSameOriginalAuxiliaryNonregular

/-! SOURCE ONLY / UNVERIFIED. Boundary actual q selection constructs BOTH
same-curve original lifts and a disjoint reduced ORIGINAL degree-three cycle
whose OWN native support stalk is proved nonregular. No supplied cycle,
jet/native surjectivity, nonregularity, integrality or GI premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual boundary construction supplies the formerly missing disjoint
singular degree-three curve cycle. Its support is the SAME AX, with own
native nonregularity derived from the actual original residue full jet.
Selected-curve geometric integrality and branch classification remain open. -/
theorem boundary_exists_selectedCurve_originalPoint_and_disjoint_singular_reducedCubic_cycle
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface p hp))
    (hPcop : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (m : ℕ) (hm : 3 ≤ m)
    (hdegree : (hypersurfaceToBase p hp).residueDegree P.1 =
      (m + 3).choose 3 - m.choose 3) :
    ∃ (A : closedPoints (hypersurface p hp)) (q : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous (m + 1)),
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧ A ≠ P ∧
      (hypersurfaceToBase p hp).residueDegree A.1 = 3 ∧
      let X := scheme (projectiveIntersectionIdeal p q hp hq)
      let i := cubicSecondEquationCurveImmersion p q hp (m + 1) hq
      ∃ (PX AX : closedPoints X) (zcycle : EffectiveZeroCycle X),
        i PX.1 = P.1 ∧ i AX.1 = A.1 ∧
        IsIso (i.residueFieldMap PX.1) ∧ IsIso (i.residueFieldMap AX.1) ∧
        (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree PX.1 =
          (hypersurfaceToBase p hp).residueDegree P.1 ∧
        (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree AX.1 = 3 ∧
        PX ≠ AX ∧ zcycle = Finsupp.single AX 1 ∧
        (∀ B ∈ zcycle.support, zcycle B = 1) ∧
        EffectiveZeroCycle.degree (toBase (projectiveIntersectionIdeal p q hp hq)) zcycle = 3 ∧
        PX ∉ zcycle.support ∧
        (∀ B ∈ zcycle.support, ¬ IsRegularLocalRing (X.presheaf.stalk B.1)) := by
  classical
  obtain ⟨A, q, hq, hqnot, hAP, hAdegree, PX, AX, zcycle,
      hPX, hAX, hPXresidue, hAXresidue, hPXdegree, hAXdegree,
      hdisjoint, hzsingle, hred, hzdegree, hPoutside, hjetdata⟩ :=
    boundary_exists_selectedCurve_originalPoint_and_disjoint_reducedCubic_cycle
      p hp hp0 P hPcop hno m hm hdegree
  let S := hypersurface p hp
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI := pointAlgebra (hypersurfaceToBase p hp) A.1
  obtain ⟨anchor, g, pivot, hgbase, hgpoint, _hx, _heval, _hpzero, hpivot, hqjet⟩ := hjetdata
  have hsing : ¬ IsRegularLocalRing (X.presheaf.stalk AX.1) :=
    (selectedCurve_sameOriginalAuxiliaryPoint_cotangent_ge_two_and_nonregular
      (K := K) p q hp hp0 (m + 1) hq hqnot A AX hAX
      anchor g hgbase hgpoint pivot hpivot hqjet).2
  refine ⟨A, q, hq, hqnot, hAP, hAdegree, PX, AX, zcycle,
    hPX, hAX, hPXresidue, hAXresidue, hPXdegree, hAXdegree,
    hdisjoint, hzsingle, hred, hzdegree, hPoutside, ?_⟩
  intro B hB
  have hBA : B = AX := by
    simpa only [hzsingle, Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] using hB
  subst B
  exact hsing

end PfaffianDescent.Coray
