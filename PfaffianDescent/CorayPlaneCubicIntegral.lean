import AllCharacteristics.SmoothSchemeRegularity
import AllCharacteristics.ProjectiveBaseChange
import AllCharacteristics.ProjectiveFiberSmoothness
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! SOURCE ONLY / UNVERIFIED150. Native Fin3 polynomial prime ideal gives a
generic point; native smoothness gives reduced stalks. Literal hypersurface
base-change isomorphisms transfer these facts to all categorical field fibers.
Actual original-cubic callers construct the prime/nonempty/smooth inputs. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The literal three-variable cubic principal ideal is prime when its
actual equation is irreducible. -/
theorem planeCubic_principalIdeal_prime_of_irreducible
    {K : Type u} [Field K] (q : MvPolynomial (Fin 3) K) (hq : Irreducible q) :
    (Ideal.span ({q} : Set (MvPolynomial (Fin 3) K))).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime hq.prime

/-- A nonempty smooth cubic with prime equation ideal is integral.  The prime
coordinate ring supplies the generic point of its projective spectrum, and
smoothness supplies reducedness through the local rings. -/
theorem planeCubic_isIntegral_of_smooth_of_principalIdeal_prime
    {K : Type u} [Field K] (p : MvPolynomial (Fin 3) K)
    (hp : p.IsHomogeneous 3)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 3) K))).IsPrime)
    [Nonempty (hypersurface p hp)] [Smooth (hypersurfaceToBase p hp)] :
    IsIntegral (hypersurface p hp) := by
  let I := equationIdeal p hp
  letI : IsDomain (CoordinateRing I) := by
    change IsDomain (MvPolynomial (Fin 3) K ⧸ (Ideal.span ({p} : Set _)))
    exact (Ideal.Quotient.isDomain_iff_prime _).mpr hprime
  letI : IrreducibleSpace (hypersurface p hp) := by
    let eta : ProjectiveSpectrum (grading I) :=
      ⟨⊥, by
        rw [HomogeneousIdeal.toIdeal_bot]
        exact Ideal.isPrime_bot, by
        obtain ⟨x⟩ := (inferInstance : Nonempty (hypersurface p hp))
        change ProjectiveSpectrum (grading I) at x
        intro h
        apply x.not_irrelevant_le
        exact h.trans bot_le⟩
    change IrreducibleSpace (ProjectiveSpectrum (grading I))
    rw [irreducibleSpace_def]
    exact (show IsGenericPoint eta Set.univ from by
      rw [isGenericPoint_iff_specializes]
      intro y
      simp only [Set.mem_univ, iff_true]
      apply specializes_iff_mem_closure.mpr
      apply (ProjectiveSpectrum.le_iff_mem_closure (grading I) eta y).mp
      change (⊥ : HomogeneousIdeal (grading I)) ≤ y.asHomogeneousIdeal
      exact bot_le).isIrreducible
  letI : IsReduced (hypersurface p hp) := by
    letI : ∀ x : hypersurface p hp,
        _root_.IsReduced ((hypersurface p hp).presheaf.stalk x) := fun x => by
      letI : IsDomain ((hypersurface p hp).presheaf.stalk x) :=
        isDomain_stalk_of_smooth_toSpec_field (hypersurfaceToBase p hp) x
      letI : NoZeroDivisors ((hypersurface p hp).presheaf.stalk x) :=
        IsDomain.to_noZeroDivisors _
      exact isReduced_of_noZeroDivisors
    exact isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Native geometric integrality of the SAME plane equation, from actual
prime ideals for all coefficient-field changes. This is a conversion theorem:
the original-cubic caller below constructs those primes internally. -/
theorem planeCubic_geometricallyIntegral_of_smooth_of_map_prime
    {K : Type u} [Field K]
    (q : MvPolynomial (Fin 3) K) (hq : q.IsHomogeneous 3)
    (hprime : ∀ (M : Type u) [Field M] (f : K →+* M),
      (Ideal.span ({q.map f} : Set (MvPolynomial (Fin 3) M))).IsPrime)
    [Nonempty (hypersurface q hq)] [Smooth (hypersurfaceToBase q hq)] :
    GeometricallyIntegral (hypersurfaceToBase q hq) := by
  rw [GeometricallyIntegral.eq_geometrically]
  intro L _ y Z fst snd h
  obtain ⟨f, rfl⟩ := Spec.map_surjective y
  let PB : Scheme := Limits.pullback (hypersurfaceToBase q hq)
    (Spec.map (CommRingCat.ofHom f.hom))
  letI : Nonempty PB := inferInstance
  let e := hypersurfaceBaseChangeIso f.hom q hq
  letI : Nonempty (hypersurface (q.map f.hom) (hq.map f.hom)) :=
    ⟨e.inv (Nonempty.some inferInstance)⟩
  letI : Smooth (hypersurfaceToBase (q.map f.hom) (hq.map f.hom)) :=
    smooth_hypersurfaceToBase_map f.hom q hq
  letI : IsIntegral (hypersurface (q.map f.hom) (hq.map f.hom)) :=
    planeCubic_isIntegral_of_smooth_of_principalIdeal_prime _ _ (hprime L f.hom)
  letI : IsIntegral PB := IsIntegral.of_isIso e.hom
  exact IsIntegral.of_isIso h.isoPullback.inv

end PfaffianDescent.Coray
