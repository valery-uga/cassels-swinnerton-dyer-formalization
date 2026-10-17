import PfaffianDescent.CorayFiniteActualComponentDegreeSum
import PfaffianDescent.CorayGeometricComponentHilbertEquality
import PfaffianDescent.CorayHomogeneousProjectiveComponentBijection
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Actual geometric component count times actual common degree

The finite family is constructed from ALL actual raw minimal primes over Ω,
by their genuine homogeneous cores. Its cardinal is identified with all native
projective irreducible components by the accepted component bijection. Genuine
coefficient action/splitting derives a common intrinsic degree. Actual finite
union geometry then bounds r times that degree. The smooth cubic/q geometry
is stated over Ω here; no arbitrary finite extension count replaces geometric r.
SOURCE ONLY / UNVERIFIED; root owns compiler/audit.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry TopologicalSpace MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual geometric r and the OWN intrinsic degree of a selected actual
Ω-minimal component satisfy r*μ≤3n. Every family, cardinal and common-degree
comparison is derived. Natural smooth cubic/q geometry is on the literal
Ω-extension here; original coefficient transport is a separate caller. -/
theorem originalPrime_geometricComponents_card_mul_degree_bound
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [IsGalois K Ω]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ I)
    (p q : MvPolynomial (Fin 4) Ω) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) Ω)))
    (hPQI : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤
      (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal)
    (P : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Ω))
    (hP : P.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes) :
    Nat.card (irreducibleComponents (scheme
      (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))))) *
        actualCurveCoordinateHilbertDegree P ≤ 3 * n := by
  classical
  let J := I.map (componentPolynomialCoefficientMap (algebraMap K Ω))
  let T := J.toIdeal.minimalPrimes
  letI : Finite T := (Ideal.finite_minimalPrimes_of_isNoetherianRing
    (MvPolynomial (Fin 4) Ω) J.toIdeal).to_subtype
  letI : Fintype T := Fintype.ofFinite T
  let f : T → HomogeneousIdeal (homogeneousSubmodule (Fin 4) Ω) :=
    fun Q => Q.1.homogeneousCore (homogeneousSubmodule (Fin 4) Ω)
  have hunder (Q : T) : (f Q).toIdeal = Q.1 :=
    homogeneousIdeal_minimalPrime_homogeneousCore_toIdeal J Q.1 Q.2
  have hf : Function.Injective f := by
    intro Q R h
    apply Subtype.ext
    exact (hunder Q).symm.trans ((congrArg HomogeneousIdeal.toIdeal h).trans (hunder R))
  let F := Finset.univ.image f
  have hFmin : ∀ C ∈ F, C.toIdeal ∈ J.toIdeal.minimalPrimes := by
    intro C hC
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hC
    exact (hunder Q).symm ▸ Q.2
  have hFrel : ∀ C ∈ F,
      ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) Ω) ≤ C :=
    fun C hC => homogeneousCoefficientExtension_minimalPrime_relevant I hIrel C (hFmin C hC)
  obtain ⟨_hunionDegree, hsumBound, _N, _hN⟩ :=
    selectedProjectiveFiniteActualComponents_degree_sum_bound
      p q hp hp0 n hn hq hnot J hPQI F hFmin hFrel
  have hcommon : ∀ C ∈ F,
      actualCurveCoordinateHilbertDegree C = actualCurveCoordinateHilbertDegree P := by
    intro C hC
    have hvalues : (fun d => finrank Ω (grading C d)) =
        (fun d => finrank Ω (grading P d)) :=
      funext fun d => originalPrime_geometricMinimalComponents_hilbertFunction_eq
        I C P (hFmin C hC) hP d
    exact congrArg (fun h : ℕ → ℕ =>
      if hex : ∃ μ : ℕ, ∃ N : ℕ, ∀ m, N ≤ m → h (m + 1) = h m + μ
      then Nat.find hex else 0) hvalues
  have hsum : (∑ C ∈ F, actualCurveCoordinateHilbertDegree C) =
      F.card * actualCurveCoordinateHilbertDegree P := by
    calc
      _ = ∑ _C ∈ F, actualCurveCoordinateHilbertDegree P := Finset.sum_congr rfl hcommon
      _ = _ := by simp
  have hcardRaw : F.card = Nat.card T := by
    simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using
      Finset.card_image_of_injective (Finset.univ : Finset T) hf
  have hcardProj : Nat.card T = Nat.card (irreducibleComponents (scheme J)) :=
    Nat.card_congr (homogeneousCoefficientExtension_minimalPrimesEquivProjectiveComponents
      (E := Ω) I hIrel)
  rw [hsum, hcardRaw, hcardProj] at hsumBound
  exact hsumBound

end PfaffianDescent.Coray
