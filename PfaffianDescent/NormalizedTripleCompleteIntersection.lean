import PfaffianDescent.NormalizedProjectiveQuotientFactor
import PfaffianDescent.TripleCompleteIntersectionToHypersurface

/-!
# Normalized finite points in triple complete intersections

This file upgrades coordinate vanishing for a specified finite projective
point to an actual closed immersion into the chosen complete intersection.
The resulting map remains identified with the original point on the ambient
hypersurface.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

section

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A normalized finite point on a projective cubic lifts to an actual closed
point of a selected three-cubic complete intersection whenever the two added
cubics vanish on its specified coordinates. -/
theorem normalizedPointAt_tripleCompleteIntersectionEmbedding
    (p q r : MvPolynomial (Fin 4) K)
    {a b c : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (x : Fin 4 → A)
    (hpx : p.eval₂ (algebraMap K A) x = 0)
    (hqx : q.eval₂ (algebraMap K A) x = 0)
    (hrx : r.eval₂ (algebraMap K A) x = 0)
    (z : CoordinateRing (equationIdeal p hp))
    (hz : z ∈ grading (equationIdeal p hp) 1)
    (heI : ∀ s ∈ (equationIdeal p hp).toIdeal,
      (eval₂Hom (algebraMap K A) x) s = 0)
    (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K A) x) heI) z = 1)
    (hgen : Function.Surjective (eval₂Hom (algebraMap K A) x)) :
    ∃ j : Spec (.of A) ⟶
        scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
      IsClosedImmersion j ∧
      j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
        linearNormalizedPointAt (equationIdeal p hp) x
          heI z hz hzOne := by
  let J := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let hIJ : (equationIdeal p hp).toIdeal ≤ J.toIdeal :=
    equationIdeal_le_tripleCompleteIntersectionIdeal p q r hp hq hr
  let heJ : ∀ s ∈ J.toIdeal, (eval₂Hom (algebraMap K A) x) s = 0 := by
    intro s hs
    change s.eval₂ (algebraMap K A) x = 0
    exact eval₂_vanishes_on_tripleCompleteIntersectionIdeal p q r x hpx hqx hrx s hs
  have hzOneJ : (Ideal.Quotient.lift J.toIdeal
      (eval₂Hom (algebraMap K A) x) heJ)
      (gradedQuotientMap (equationIdeal p hp) J hIJ z) = 1 := by
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective z
    have hza : (eval₂Hom (algebraMap K A) x) a = 1 := by
      rw [← ha] at hzOne
      rw [Ideal.Quotient.lift_mk] at hzOne
      exact hzOne
    rw [← ha]
    change Ideal.Quotient.lift J.toIdeal
      (eval₂Hom (algebraMap K A) x) heJ (Ideal.Quotient.mk J.toIdeal a) = 1
    rw [Ideal.Quotient.lift_mk]
    exact hza
  let j := linearNormalizedPointAt J x heJ
    (gradedQuotientMap (equationIdeal p hp) J hIJ z)
    ((gradedQuotientMap (equationIdeal p hp) J hIJ).map_mem hz) hzOneJ
  refine ⟨j, ?_, ?_⟩
  · exact linearNormalizedPointAt_isClosedImmersion J x heJ
      (gradedQuotientMap (equationIdeal p hp) J hIJ z)
      ((gradedQuotientMap (equationIdeal p hp) J hIJ).map_mem hz)
      hzOneJ hgen
  · change j ≫ schemeQuotientMap (equationIdeal p hp) J hIJ =
      linearNormalizedPointAt (equationIdeal p hp) x heI z hz hzOne
    exact linearNormalizedPointAt_comp_schemeQuotientMap (equationIdeal p hp) J hIJ x heI heJ z hz
      hzOne hzOneJ

/-- Transport the normalized complete-intersection embedding from the affine
coordinate algebra back to the finite affine scheme from which those
coordinates were reconstructed. -/
theorem normalizedPointAt_tripleCompleteIntersectionEmbedding_of_isoSpec
    {Z : Scheme.{u}} [IsAffine Z] [Algebra K Γ(Z, ⊤)] [Module.Finite K Γ(Z, ⊤)]
    (p q r : MvPolynomial (Fin 4) K)
    {a b c : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b) (hr : r.IsHomogeneous c)
    (i : Z ⟶ hypersurface p hp)
    (x : Fin 4 → Γ(Z, ⊤))
    (hpx : p.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0)
    (hqx : q.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0)
    (hrx : r.eval₂ (algebraMap K Γ(Z, ⊤)) x = 0)
    (z : CoordinateRing (equationIdeal p hp))
    (hz : z ∈ grading (equationIdeal p hp) 1)
    (heI : ∀ s ∈ (equationIdeal p hp).toIdeal,
      (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) s = 0)
    (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K Γ(Z, ⊤)) x) heI) z = 1)
    (hgen : Function.Surjective (eval₂Hom (algebraMap K Γ(Z, ⊤)) x))
    (hpoint : linearNormalizedPointAt (equationIdeal p hp) x heI z hz hzOne =
      Z.isoSpec.inv ≫ i) :
    ∃ j : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr),
      IsClosedImmersion j ∧
      j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr = i := by
  obtain ⟨j₀, hj₀closed, hj₀⟩ :=
    normalizedPointAt_tripleCompleteIntersectionEmbedding p q r hp hq hr x
      hpx hqx hrx z hz heI hzOne hgen
  let j := Z.isoSpec.hom ≫ j₀
  refine ⟨j, ?_, ?_⟩
  · dsimp [j]
    infer_instance
  · dsimp [j]
    rw [Category.assoc, hj₀, hpoint]
    simp only [Category.assoc, Z.isoSpec.hom_inv_id_assoc]

end

end PfaffianDescent
