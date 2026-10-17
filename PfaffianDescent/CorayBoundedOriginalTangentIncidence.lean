import PfaffianDescent.CorayLinearTangentIncidence
import PfaffianDescent.CorayBoundedOriginalSectionFamily
import PfaffianDescent.CorayFullJetDifferentials

/-! Source-only, unverified. Coray's tangent-incidence obstruction on the
ACTUAL bounded-degree through-P cubic section family. The auxiliary full
jet lies on the cubic, but no chosen q transversality is assumed. The
criterion is an equivalence; actual line incidence must avoid its bad side. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

section
variable {K L M : Type u} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M]

/-- Tangent value of an actual quotient-grade section in an actual full
surface jet. The jet incidence with p is the only condition; the tangent
value of a chosen section is not presumed nonzero. -/
def cubicGradeTangentRestriction
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (z : Fin 4 → M) (v : Fin 2 → Fin 4 → M)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v) = 0) :
    grading (equationIdeal p hp) n →ₗ[K] (Fin 2 → M) :=
  ((TrivSqZeroExt.sndHom M (Fin 2 → M)).restrictScalars K).comp
    (cubicGradeCoordinateEvaluation p hp n (surfacePlaneJetCoordinates z v) hpJ)

/-- The concrete tangent values are exactly the two original-K
homogeneous directional derivative evaluations. This gives matrix entries
for the future actual bad-line incidence equations. -/
theorem surfacePlaneJet_tangent_value_eq_directional_derivative
    (z : Fin 4 → M) (v : Fin 2 → Fin 4 → M)
    (q : MvPolynomial (Fin 4) K) (r : Fin 2) :
    (q.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v)).snd r =
      ∑ i : Fin 4, (pderiv i q).eval₂ (algebraMap K M) z * v r i := by
  have h := congrArg TrivSqZeroExt.snd
    (surfacePlaneJet_projects_to_directionalJet z v r q)
  simpa only [TrivSqZeroExt.snd_map, LinearMap.proj_apply,
    homogeneousDirectionalJet_snd, MvPolynomial.aeval_def] using h

/-- The same actual through-P family is restricted at the auxiliary
residue coordinates; the original K action is retained. -/
def cubicThroughPointAuxiliaryEvaluation
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (z : Fin 4 → M) (hpz : p.eval₂ (algebraMap K M) z = 0) :
    cubicThroughCoordinateSections p hp n y hpy →ₗ[K] M :=
  (cubicGradeCoordinateEvaluation p hp n z hpz).domRestrict _

/-- The first-order map is restricted to exactly the SAME bounded family,
with its actual quotient-grade carrier. -/
def cubicThroughPointAuxiliaryTangentRestriction
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (z : Fin 4 → M) (v : Fin 2 → Fin 4 → M)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v) = 0) :
    cubicThroughCoordinateSections p hp n y hpy →ₗ[K] (Fin 2 → M) :=
  (cubicGradeTangentRestriction p hp n z v hpJ).domRestrict _

/-- The exact bounded-family tangent bad incidence is the inclusion of
actual K-linear tangent functionals in the ordinary evaluation span.
No good-position or desired regularity premise is present. -/
theorem cubicThroughPoint_tangent_incidence_iff
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (z : Fin 4 → M) (hpz : p.eval₂ (algebraMap K M) z = 0)
    (v : Fin 2 → Fin 4 → M)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v) = 0) :
    (∃ s : cubicThroughCoordinateSections p hp n y hpy,
      cubicThroughPointAuxiliaryEvaluation p hp n y hpy z hpz s = 0 ∧
      cubicThroughPointAuxiliaryTangentRestriction p hp n y hpy z v hpJ s ≠ 0) ↔
      ¬ LinearMap.range
          (cubicThroughPointAuxiliaryTangentRestriction p hp n y hpy z v hpJ).dualMap ≤
        LinearMap.range
          (cubicThroughPointAuxiliaryEvaluation p hp n y hpy z hpz).dualMap :=
  exists_vanishing_section_with_tangent_ne_zero_iff
    (K := K) (V := cubicThroughCoordinateSections p hp n y hpy)
    (A := M) (T := Fin 2 → M)
    (cubicThroughPointAuxiliaryEvaluation p hp n y hpy z hpz)
    (cubicThroughPointAuxiliaryTangentRestriction p hp n y hpy z v hpJ)

/-- The same criterion has ACTUAL homogeneous polynomial outputs of the
prescribed degree: both original residue values vanish, the original full
jet has nonzero tangent value, and the cubic does not divide q. This is
still an equivalence, not a joint-selector existence assertion. -/
theorem cubicThroughPoint_polynomial_tangent_incidence_iff
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (n : ℕ)
    (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (z : Fin 4 → M) (hpz : p.eval₂ (algebraMap K M) z = 0)
    (v : Fin 2 → Fin 4 → M)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v) = 0) :
    (∃ q : MvPolynomial (Fin 4) K,
      q.IsHomogeneous n ∧ q.eval₂ (algebraMap K L) y = 0 ∧
      q.eval₂ (algebraMap K M) z = 0 ∧
      (q.eval₂ (algebraMap K (SurfacePlaneJet M))
        (surfacePlaneJetCoordinates z v)).snd ≠ 0 ∧
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))) ↔
      ¬ LinearMap.range
          (cubicThroughPointAuxiliaryTangentRestriction p hp n y hpy z v hpJ).dualMap ≤
        LinearMap.range
          (cubicThroughPointAuxiliaryEvaluation p hp n y hpy z hpz).dualMap := by
  rw [← cubicThroughPoint_tangent_incidence_iff p hp n y hpy z hpz v hpJ]
  constructor
  · rintro ⟨q, hq, hy, hz, hD, hnot⟩
    let s : grading (equationIdeal p hp) n :=
      ⟨Ideal.Quotient.mk (equationIdeal p hp).toIdeal q,
        show Ideal.Quotient.mk (equationIdeal p hp).toIdeal q ∈
          (homogeneousSubmodule (Fin 4) K n).map
            (Ideal.Quotient.mkₐ K (equationIdeal p hp).toIdeal).toLinearMap from
          ⟨q, hq, rfl⟩⟩
    have hs : s ∈ cubicThroughCoordinateSections p hp n y hpy := by
      apply (cubicThroughCoordinateSections_mem_iff p hp n y hpy s).mpr
      exact ⟨q, hq, hy, rfl⟩
    refine ⟨⟨s, hs⟩, ?_, ?_⟩
    · exact hz
    · exact hD
  · rintro ⟨s, hz, hD⟩
    obtain ⟨q, hq, hy, hqs⟩ :=
      (cubicThroughCoordinateSections_mem_iff p hp n y hpy s.1).mp s.2
    refine ⟨q, hq, hy, ?_, ?_, ?_⟩
    · change cubicCoordinateAlgebraEvaluation p hp z hpz s.1.1 = 0 at hz
      rw [← hqs] at hz
      exact hz
    · change (cubicCoordinateAlgebraEvaluation p hp
          (surfacePlaneJetCoordinates z v) hpJ s.1.1).snd ≠ 0 at hD
      rw [← hqs] at hD
      exact hD
    · intro hmem
      have hsval : s.1.1 = 0 := hqs.symm.trans
        (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)
      have hs0 : s = 0 := Subtype.ext (Subtype.ext hsval)
      exact hD (by rw [hs0, map_zero])

end
end PfaffianDescent.Coray
end
