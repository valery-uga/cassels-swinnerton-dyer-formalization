import PfaffianDescent.CorayRegularPairLinearSectionAvoidance
import PfaffianDescent.CorayProjectiveGlobalNormalizationSupport
import PfaffianDescent.CoraySmoothCurveHilbert

/-! ACTUAL choice of a third regular linear equation avoiding the actual
finite normalization quotient support on SAME selected curve. Finiteness,
associated-prime avoidance and literal cone nonzerodivisor are constructed,
not supplied. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A smooth cubic and its genuine nonmultiple q admit an original linear
H which is regular modulo literal (p,q) and avoids every point of the OWN
actual normalization quotient support. No geometric integrality required. -/
theorem projectiveIntersection_exists_regular_linear_avoiding_actualNormalizationQuotientSupport
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    ∃ H : MvPolynomial (Fin 4) K, H.IsHomogeneous 1 ∧
      (∀ x : MvPolynomial (Fin 4) K,
        H * x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) ∧
      (∀ x ∈ schemeModuleStalkSupport (genericNormalizationQuotientSheaf X),
        Ideal.Quotient.mk I.toIdeal H ∉ x.asHomogeneousIdeal) := by
  classical
  intro I X
  let C := schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)
  have hfinite : C.Finite :=
    projectiveIntersection_genericNormalizationQuotient_stalkSupport_finite p q hp hp0 n hq hnot
  letI : Fintype C := hfinite.fintype
  obtain ⟨H, hH, hregular, havoid⟩ :=
    regular_pair_exists_linear_nonzerodivisor_avoiding_finite_projective_family
      p q hp hq hp0 (isRelPrime_of_smooth_cubic_and_not_mem p q hp hp0 hnot)
      (fun x : C => x.1)
  exact ⟨H, hH, hregular, fun x hx => havoid ⟨x, hx⟩⟩

end PfaffianDescent.Coray
