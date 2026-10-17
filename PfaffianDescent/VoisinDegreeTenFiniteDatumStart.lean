import PfaffianDescent.VoisinFiniteSubschemeDatumResidual
import PfaffianDescent.CubicFiniteSubschemeHyperplane
import PfaffianDescent.NormalizedTripleCompleteIntersection
import PfaffianDescent.TripleCompleteIntersectionJacobian
import AllCharacteristics.DisjointFiniteSubschemeUnionCycle

/-!
# The finite-subscheme start of Voisin's degree-ten reduction

This packages the actual rank-sixteen datum made from a degree-ten datum and
two degree-three data, and feeds it to the first complete-intersection
residual construction.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

variable {K : Type u} [Field K] [Infinite K]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def degreeTenAndTwoDegreeThreeDatum
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (D₁₀ : FiniteSubschemeDatum f 10)
    (D₃ : FiniteSubschemeDatum f 3) (D₃' : FiniteSubschemeDatum f 3)
    (h₁₂ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₁₀))
      (Set.range (finiteSubschemeDatumSpecMap f D₃)))
    (h₁₂₃ : Disjoint (Set.range
      (disjointSpecUnionMap (finiteSubschemeDatumSpecMap f D₁₀)
        (finiteSubschemeDatumSpecMap f D₃)))
      (Set.range (finiteSubschemeDatumSpecMap f D₃'))) :
    FiniteSubschemeDatum f 16 :=
  finiteSubschemeDatum_rankSixteenOfDegreeTenAndTwoDegreeThree
    f D₁₀ D₃ D₃' h₁₂ h₁₂₃

theorem degreeTenAndTwoDegreeThreeDatum_cycle
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (D₁₀ : FiniteSubschemeDatum f 10)
    (D₃ : FiniteSubschemeDatum f 3) (D₃' : FiniteSubschemeDatum f 3)
    (h₁₂ : Disjoint (Set.range (finiteSubschemeDatumSpecMap f D₁₀))
      (Set.range (finiteSubschemeDatumSpecMap f D₃)))
    (h₁₂₃ : Disjoint (Set.range
      (disjointSpecUnionMap (finiteSubschemeDatumSpecMap f D₁₀)
        (finiteSubschemeDatumSpecMap f D₃)))
      (Set.range (finiteSubschemeDatumSpecMap f D₃'))) :
    finiteSubschemeDatumCycle f
      (degreeTenAndTwoDegreeThreeDatum f D₁₀ D₃ D₃' h₁₂ h₁₂₃) =
      finiteSubschemeDatumCycle f D₁₀ + finiteSubschemeDatumCycle f D₃ +
        finiteSubschemeDatumCycle f D₃' := by
  exact finiteSubschemeDatumCycle_rankSixteenOfDegreeTenAndTwoDegreeThree
    f D₁₀ D₃ D₃' h₁₂ h₁₂₃

/-- The precise base-locus condition in Voisin's first residual step, stated
on one actual completion of a degree-ten datum.  It says that the cubic
system through the sixteen points has positive codimension in the restriction
to every associated prime of each selected cubic--cubic quotient.  Lemma 3.3
is the geometric proof of this condition for the moving configuration. -/
def DegreeTenCompletionThirdCubicFinrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀) : Prop :=
  let D := C.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∀ (x : Fin 4 → Γ(D.val.subscheme, ⊤)),
  Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) →
  ∀ (q : MvPolynomial (Fin 4) K),
  let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
  let W := homogeneousVanishingPolynomialSubmodule
    (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 3
  let qmap : MvPolynomial (Fin 4) K →ₗ[K]
      MvPolynomial (Fin 4) K ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
  let V : Submodule K (MvPolynomial (Fin 4) K ⧸ I) := W.map qmap
  ∀ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
      (MvPolynomial (Fin 4) K ⧸ I),
    Module.finrank K ((P.restrictScalars K).comap V.subtype) <
      Module.finrank K V

/-- The associated-component formulation of the base-locus assertion in
Voisin's Lemma 3.3.  It says directly that the cubic system through the
rank-sixteen completion has a member nonzero on every associated component
of each cubic--cubic intersection.  This is the geometric condition; the
finite-rank inequality used by the residual construction follows formally. -/
def DegreeTenCompletionThirdCubicAvoidsAssociatedPrimes
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀) : Prop :=
  let D := C.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∀ (x : Fin 4 → Γ(D.val.subscheme, ⊤)),
  Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) →
  ∀ (q : MvPolynomial (Fin 4) K),
  let I := Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
  let W := homogeneousVanishingPolynomialSubmodule
    (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 3
  ∀ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
      (MvPolynomial (Fin 4) K ⧸ I),
    ∃ r ∈ W, Ideal.Quotient.mk I r ∉ P

/-- Associated-component avoidance implies the finite-rank base-locus drop
needed by the first residual construction. -/
theorem DegreeTenCompletionThirdCubicAvoidsAssociatedPrimes.finrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (havoid : DegreeTenCompletionThirdCubicAvoidsAssociatedPrimes p hp D₁₀ C) :
    DegreeTenCompletionThirdCubicFinrankDrop p hp D₁₀ C := by
  let D := C.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  intro x hx q
  exact finrank_drop_of_avoids_associatedPrimes_mod_ideal
    (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (homogeneousVanishingPolynomialSubmodule
      (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 3)
    (havoid x hx q)

/-- The finite-rank condition is not an additional approximation: it is
equivalent to associated-component avoidance.  This reverses the linear
algebra packaging and leaves the geometric proof of Lemma 3.3 with its
natural noncontainment statement. -/
theorem DegreeTenCompletionThirdCubicAvoidsAssociatedPrimes.of_finrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (hdrop : DegreeTenCompletionThirdCubicFinrankDrop p hp D₁₀ C) :
    DegreeTenCompletionThirdCubicAvoidsAssociatedPrimes p hp D₁₀ C := by
  let D := C.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  intro x hx q
  exact (avoids_associatedPrimes_mod_ideal_iff_finrank_drop
    (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (homogeneousVanishingPolynomialSubmodule
      (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 3)).mpr
    (hdrop x hx q)

/-- Equivalent formulations of Voisin's Lemma 3.3 base-locus conclusion for
one completed degree-ten datum. -/
theorem degreeTenCompletionThirdCubic_avoidsAssociatedPrimes_iff_finrankDrop
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀) :
    DegreeTenCompletionThirdCubicAvoidsAssociatedPrimes p hp D₁₀ C ↔
      DegreeTenCompletionThirdCubicFinrankDrop p hp D₁₀ C := by
  constructor
  · exact DegreeTenCompletionThirdCubicAvoidsAssociatedPrimes.finrankDrop p hp D₁₀ C
  · exact DegreeTenCompletionThirdCubicAvoidsAssociatedPrimes.of_finrankDrop p hp D₁₀ C

/- Voisin's selected third-cubic argument only needs finitely many possible
   first cubics at a time.  These family forms retain that weaker scope
   explicitly, rather than silently replacing it by the uniform condition
   above. -/
def DegreeTenCompletionThirdCubicFinrankDropFamily
    {ι : Type*} [Finite ι]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (Q : ι → MvPolynomial (Fin 4) K) : Prop :=
  let D := C.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∀ (x : Fin 4 → Γ(D.val.subscheme, ⊤)),
  Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) →
  ∀ j : ι,
  let I := Ideal.span ({p, Q j} : Set (MvPolynomial (Fin 4) K))
  let W := homogeneousVanishingPolynomialSubmodule
    (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 3
  let qmap : MvPolynomial (Fin 4) K →ₗ[K]
      MvPolynomial (Fin 4) K ⧸ I := (Ideal.Quotient.mkₐ K I).toLinearMap
  let V : Submodule K (MvPolynomial (Fin 4) K ⧸ I) := W.map qmap
  ∀ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
      (MvPolynomial (Fin 4) K ⧸ I),
    Module.finrank K ((P.restrictScalars K).comap V.subtype) <
      Module.finrank K V

def DegreeTenCompletionThirdCubicAvoidsAssociatedPrimesFamily
    {ι : Type*} [Finite ι]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (Q : ι → MvPolynomial (Fin 4) K) : Prop :=
  let D := C.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  ∀ (x : Fin 4 → Γ(D.val.subscheme, ⊤)),
  Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) →
  ∀ j : ι,
  let I := Ideal.span ({p, Q j} : Set (MvPolynomial (Fin 4) K))
  let W := homogeneousVanishingPolynomialSubmodule
    (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 3
  ∀ P ∈ associatedPrimes (MvPolynomial (Fin 4) K ⧸ I)
      (MvPolynomial (Fin 4) K ⧸ I),
    ∃ r ∈ W, Ideal.Quotient.mk I r ∉ P

theorem DegreeTenCompletionThirdCubicAvoidsAssociatedPrimesFamily.finrankDrop
    {ι : Type*} [Finite ι]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (Q : ι → MvPolynomial (Fin 4) K)
    (havoid : DegreeTenCompletionThirdCubicAvoidsAssociatedPrimesFamily
      p hp D₁₀ C Q) :
    DegreeTenCompletionThirdCubicFinrankDropFamily p hp D₁₀ C Q := by
  let D := C.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  intro x hx j
  exact finrank_drop_of_avoids_associatedPrimes_mod_ideal
    (Ideal.span ({p, Q j} : Set (MvPolynomial (Fin 4) K)))
    (homogeneousVanishingPolynomialSubmodule
      (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 3)
    (havoid x hx j)

theorem DegreeTenCompletionThirdCubicAvoidsAssociatedPrimesFamily.of_finrankDrop
    {ι : Type*} [Finite ι]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (Q : ι → MvPolynomial (Fin 4) K)
    (hdrop : DegreeTenCompletionThirdCubicFinrankDropFamily
      p hp D₁₀ C Q) :
    DegreeTenCompletionThirdCubicAvoidsAssociatedPrimesFamily p hp D₁₀ C Q := by
  let D := C.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  intro x hx j
  exact (avoids_associatedPrimes_mod_ideal_iff_finrank_drop
    (Ideal.span ({p, Q j} : Set (MvPolynomial (Fin 4) K)))
    (homogeneousVanishingPolynomialSubmodule
      (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 3)).mpr
    (hdrop x hx j)

theorem degreeTenCompletionThirdCubicFamily_avoidsAssociatedPrimes_iff_finrankDrop
    {ι : Type*} [Finite ι]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (Q : ι → MvPolynomial (Fin 4) K) :
    DegreeTenCompletionThirdCubicAvoidsAssociatedPrimesFamily p hp D₁₀ C Q ↔
      DegreeTenCompletionThirdCubicFinrankDropFamily p hp D₁₀ C Q := by
  constructor
  · exact DegreeTenCompletionThirdCubicAvoidsAssociatedPrimesFamily.finrankDrop
      p hp D₁₀ C Q
  · exact DegreeTenCompletionThirdCubicAvoidsAssociatedPrimesFamily.of_finrankDrop
      p hp D₁₀ C Q

theorem exists_degreeTenCompletionThirdCubic_of_finrankDropFamily
    {ι : Type*} [Finite ι]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (Q : ι → MvPolynomial (Fin 4) K)
    (hdrop : DegreeTenCompletionThirdCubicFinrankDropFamily
      p hp D₁₀ C Q) :
    let D := C.datum
    letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
    letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤))
      (hpx : p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
      ∃ r : MvPolynomial (Fin 4) K,
        r.IsHomogeneous 3 ∧ r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        ∀ j : ι, ∀ y : MvPolynomial (Fin 4) K,
          r * y ∈ Ideal.span ({p, Q j} : Set (MvPolynomial (Fin 4) K)) →
            y ∈ Ideal.span ({p, Q j} : Set (MvPolynomial (Fin 4) K)) := by
  let D := C.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, hpx, hxsurj, _⟩ :=
    cubicFiniteSubscheme_degree_sixteen_sections p hp hne D.val.subschemeι
      (AllCharacteristics.finiteSubschemeDatum_finiteSchemeRank
        (hypersurfaceToBase p hp) D)
  let I : ι → Ideal (MvPolynomial (Fin 4) K) := fun j =>
    Ideal.span ({p, Q j} : Set (MvPolynomial (Fin 4) K))
  obtain ⟨r, hrhom, hrvan, hrreg⟩ :=
    exists_regular_third_cubic_section_data_of_finrank_drop_family x I (by
      intro j
      simpa only [I, DegreeTenCompletionThirdCubicFinrankDropFamily, D] using
        hdrop x hxsurj j)
  refine ⟨x, hpx, hxsurj, r, hrhom, hrvan, ?_⟩
  intro j y hy
  exact hrreg j y (by simpa only [I] using hy)

/- The finite-family selector can be fed directly into the first residual
   construction.  The normalized coordinates are taken from the actual
   degree-sixteen completion, so the resulting residual is attached to that
   completion rather than merely to an abstract coordinate presentation. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_of_completion_and_finrank_drop_family
    [CharZero K] {ι : Type*} [Finite ι]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (Q : ι → MvPolynomial (Fin 4) K) (j : ι)
    (hq : (Q j).IsHomogeneous 3) (hrel : IsRelPrime p (Q j))
    (coordinates : let D := C.datum
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧
        ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        (Q j).eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    (hdrop : DegreeTenCompletionThirdCubicFinrankDropFamily
      p hp D₁₀ C Q)
    (htransverse : ∀ (r : MvPolynomial (Fin 4) K)
      (hr : r.IsHomogeneous 3),
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, Q j} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, Q j} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase
        (tripleCompleteIntersectionHomogeneousIdeal p (Q j) r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  let D := C.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  haveI := finiteSchemeCoefficient_finite
    (D.val.subschemeι ≫ hypersurfaceToBase p hp)
  obtain ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan⟩ := coordinates
  obtain ⟨r, hr, hrvan, hregular⟩ :=
    exists_regular_third_cubic_section_data_of_finrank_drop_family x
      (fun k : ι => Ideal.span ({p, Q k} : Set (MvPolynomial (Fin 4) K)))
      (by
        intro k
        simpa only [DegreeTenCompletionThirdCubicFinrankDropFamily, D] using
          hdrop x hxsurj k)
  have hq0 : Q j ≠ 0 :=
    isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hp (by decide) hrel
  have htrans := htransverse r hr (hregular j)
  let R := finiteSubschemeDatum_degree_sixteen_residual_of_selected_coordinates
    p (Q j) r hp hq hr hne hq0 hrel (hregular j) D
    ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan, hrvan⟩
  refine ⟨R, finiteSubschemeDatumCycle_degree _ _, ?_⟩
  exact finiteSubschemeDatum_degree_sixteen_residual_of_selected_coordinates_toBase_etale
    p (Q j) r hp hq hr hne hq0 hrel (hregular j) D
    ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan, hrvan⟩

/-- The associated-prime base-locus condition and a transverse third cubic
produce Voisin's actual finite étale degree-eleven residual from one
degree-ten completion.  No primeness of the intermediate cubic--cubic curve
is used. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_of_completion_and_finrank_drop
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hdrop : DegreeTenCompletionThirdCubicFinrankDrop p hp D₁₀ C)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  exact
    exists_finiteSubschemeDatum_degree_sixteen_residual_and_toBase_etale_of_prime_surface_and_finrank_drop
      p hp hne C.datum hprime hdrop htransverse

/-- A chosen transverse three-cubic triple through the degree-ten completion
produces the finite étale rank-eleven residual used by Voisin's rank-two
step.  This is the direct first-residual interface after Coray supplies a
degree-ten datum; it does not replace the chosen triple by a uniform
transversality assumption. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_of_completion_and_selected_coordinates
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (coordinates : let D := C.datum
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    (htransverse : Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  have hq0 : q ≠ 0 :=
    isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hp (by decide) hrel
  let D := C.datum
  let _ : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  let _ : Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) := htransverse
  let R := finiteSubschemeDatum_degree_sixteen_residual_of_selected_coordinates
    p q r hp hq hr hne hq0 hrel hregular D coordinates
  refine ⟨R, finiteSubschemeDatumCycle_degree _ _, ?_⟩
  exact finiteSubschemeDatum_degree_sixteen_residual_of_selected_coordinates_toBase_etale
    p q r hp hq hr hne hq0 hrel hregular D coordinates

/-- A nonzero square Jacobian on every normalized chart is the concrete
Bertini condition which supplies the transverse three-cubic intersection in
the first degree-ten residual step. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_of_completion_and_selected_coordinates_of_chartJacobian_isUnit
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (coordinates : let D := C.datum
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    (hjac : ∀ j : Fin 4,
      IsUnit (tripleCompleteIntersectionChartJacobian p q r hp hq hr j)) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  exact exists_degreeTenResidualDatum_and_toBase_etale_of_completion_and_selected_coordinates
    p q r hp hq hr hne hrel hregular D₁₀ C coordinates
    (etale_tripleCompleteIntersection_toBase_of_chartJacobian_isUnit p q r hp hq hr hjac)

/-- Voisin's associated-component avoidance statement for one selected
intermediate cubic produces the third cubic and hence the finite étale
rank-eleven residual.  This is the direct form of Lemma 3.3 used in the
degree-ten branch: it asks only that the cubic system through the completed
datum avoid every associated component of the selected cubic--cubic curve.
Neither a prime intermediate curve nor a uniform condition over unrelated
coordinate choices is required. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_of_completion_and_avoids_associatedPrimes
    [CharZero K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hne : p ≠ 0)
    (hrel : IsRelPrime p q)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (coordinates : let D := C.datum
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        (∀ P ∈ associatedPrimes
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
          (MvPolynomial (Fin 4) K ⧸ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))),
          ∃ r ∈ homogeneousVanishingPolynomialSubmodule
            (K := K) (A := Γ(D.val.subscheme, ⊤)) (sigma := Fin 4) x 3,
            Ideal.Quotient.mk (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) r ∉ P))
    (htransverse : ∀ (r : MvPolynomial (Fin 4) K)
      (hr : r.IsHomogeneous 3),
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  exact
    exists_finiteSubschemeDatum_degree_sixteen_residual_and_toBase_etale_of_selected_avoids_associatedPrimes
      p q hp hq hne hrel C.datum coordinates htransverse

/-- The point-specific first Bertini step after completing the degree-ten
datum. A single selected regular transverse cubic yields the rank-eleven
residual, with no universal transversality condition on the cubic system. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_of_completion_and_selected_regular_transverse_cubic
    [CharZero K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (hne : p ≠ 0) (hrel : IsRelPrime p q)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (selected : let D := C.datum
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell r : MvPolynomial (Fin 4) K)
        (hr : r.IsHomogeneous 3),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        (∀ y : MvPolynomial (Fin 4) K,
          r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
            y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) ∧
        Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  exact
    exists_finiteSubschemeDatum_degree_sixteen_residual_and_toBase_etale_of_selected_regular_transverse_cubic
      p q hp hq hne hrel C.datum selected

/-- The first residual after completing a degree-ten datum needs only the
Frobenius structure of its selected three-cubic intersection to give a
finite-flat degree-eleven datum. -/
theorem exists_degreeTenResidualDatum_of_completion_and_selected_coordinates_of_frobenius
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (coordinates : let D := C.datum
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0)
    (hfrob :
      letI := triple_cubic_intersection_finite
        p q r hp hq hr hne
          (isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hp (by decide) hrel)
          hrel hregular
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr), ⊤),
        IsFrobeniusFunctional ell) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 := by
  have hq0 : q ≠ 0 :=
    isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hp (by decide) hrel
  let D := C.datum
  letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
  let R := finiteSubschemeDatum_degree_sixteen_residual_of_selected_coordinates_of_frobenius
    p q r hp hq hr hne hq0 hrel hregular D coordinates hfrob
  exact ⟨R, finiteSubschemeDatumCycle_degree _ _⟩

/-- An actual embedding of the completed degree-ten datum in a selected
three-cubic complete intersection is enough to produce Voisin's first
residual.  This is the scheme-theoretic form of the condition that the three
selected cubics contain the completed subscheme: no separate choice of
projective coordinates is retained. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_of_completion_and_completeIntersectionEmbedding
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (j : C.datum.val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      C.datum.val.subschemeι)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  let R := finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding
    p q r hp hq hr hne hq0 hrel hregular C.datum j hj
  refine ⟨R, finiteSubschemeDatumCycle_degree _ _, ?_⟩
  exact finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding_toBase_etale
    p q r hp hq hr hne hq0 hrel hregular C.datum j hj

/-- The first residual datum constructed from a completed degree-ten point
is automatically disjoint from that completion.  This is the exact
support-separation field needed by the first of Voisin's three pencils, and
is now a consequence of the transverse complete-intersection construction. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_completion_and_completeIntersectionEmbedding
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (j : C.datum.val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      C.datum.val.subschemeι)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) C.datum))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  let R := finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding
    p q r hp hq hr hne hq0 hrel hregular C.datum j hj
  refine ⟨R, finiteSubschemeDatumCycle_degree _ _, ?_, ?_⟩
  · exact finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding_toBase_etale
      p q r hp hq hr hne hq0 hrel hregular C.datum j hj
  · exact (disjoint_finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding
      p q r hp hq hr hne hq0 hrel hregular C.datum j hj).symm

/-- A reduced regular three-cubic intersection over a characteristic-zero
field is already finite étale.  Thus reducedness supplies the transversality
input needed for the first degree-ten residual and its support separation. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_completion_and_reduced_completeIntersectionEmbedding
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (j : C.datum.val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      C.datum.val.subschemeι)
    [AlgebraicGeometry.IsReduced (scheme
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
      Disjoint
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) C.datum))
        (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) R)) := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  letI : IsFinite (toBase I) := triple_cubic_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  letI : Etale (toBase I) := finiteScheme_etale_of_isReduced (toBase I)
  exact
    exists_degreeTenResidualDatum_and_toBase_etale_and_disjoint_of_completion_and_completeIntersectionEmbedding
      p q r hp hq hr hne hq0 hrel hregular D₁₀ C j hj

/-- The same complete-intersection embedding needs only a Frobenius
functional on the finite intersection to produce the rank-eleven datum.
This separates the length calculation from the later étaleness requirement
of Voisin's rank-two step. -/
theorem exists_degreeTenResidualDatum_of_completion_and_completeIntersectionEmbedding_of_frobenius
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (j : C.datum.val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      C.datum.val.subschemeι)
    (hfrob :
      letI := triple_cubic_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr), ⊤),
        IsFrobeniusFunctional ell) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 := by
  let R :=
    finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding_of_frobenius
      p q r hp hq hr hne hq0 hrel hregular C.datum j hj hfrob
  exact ⟨R, finiteSubschemeDatumCycle_degree _ _⟩

noncomputable def degreeTenAndTwoDegreeThreeResidualDatum
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (D₃ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (D₃' : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (h₁₂ : Disjoint (Set.range
      (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
    (h₁₂₃ : Disjoint (Set.range
      (disjointSpecUnionMap
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀)
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃')))
    (j : (degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
      D₁₀ D₃ D₃' h₁₂ h₁₂₃).val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      (degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
        D₁₀ D₃ D₃' h₁₂ h₁₂₃).val.subschemeι)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    FiniteSubschemeDatum (hypersurfaceToBase p hp) 11 :=
  finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding
    p q r hp hq hr hne hq0 hrel hregular
    (degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
      D₁₀ D₃ D₃' h₁₂ h₁₂₃) j hj

/-- With an explicit embedding of the completed datum, the first residual
requires only the Frobenius functional of the three-cubic intersection. -/
noncomputable def degreeTenAndTwoDegreeThreeResidualDatum_of_frobenius
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (D₃ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (D₃' : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (h₁₂ : Disjoint (Set.range
      (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
    (h₁₂₃ : Disjoint (Set.range
      (disjointSpecUnionMap
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀)
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃')))
    (j : (degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
      D₁₀ D₃ D₃' h₁₂ h₁₂₃).val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      (degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
        D₁₀ D₃ D₃' h₁₂ h₁₂₃).val.subschemeι)
    (hfrob :
      letI := triple_cubic_intersection_finite
        p q r hp hq hr hne hq0 hrel hregular
      letI := finiteSchemeCoefficientAlgebra
        (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
      ∃ ell : Module.Dual K
          Γ(scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr), ⊤),
        IsFrobeniusFunctional ell) :
    FiniteSubschemeDatum (hypersurfaceToBase p hp) 11 :=
  finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding_of_frobenius
    p q r hp hq hr hne hq0 hrel hregular
    (degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
      D₁₀ D₃ D₃' h₁₂ h₁₂₃) j hj hfrob

/-- The actual rank-eleven datum obtained after adjoining two rank-three line
sections to a degree-ten datum and taking a transverse three-cubic residual
is finite étale. This is the precise finite scheme that feeds Voisin's
rank-two construction. -/
theorem degreeTenAndTwoDegreeThreeResidualDatum_toBase_etale
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (D₃ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (D₃' : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (h₁₂ : Disjoint (Set.range
      (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
    (h₁₂₃ : Disjoint (Set.range
      (disjointSpecUnionMap
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀)
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃')))
    (j : (degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
      D₁₀ D₃ D₃' h₁₂ h₁₂₃).val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      (degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
        D₁₀ D₃ D₃' h₁₂ h₁₂₃).val.subschemeι)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    Etale ((degreeTenAndTwoDegreeThreeResidualDatum
      p q r hp hq hr hne hq0 hrel hregular D₁₀ D₃ D₃' h₁₂ h₁₂₃ j hj).val.subschemeι ≫
        hypersurfaceToBase p hp) := by
  exact finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding_toBase_etale
    p q r hp hq hr hne hq0 hrel hregular
    (degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
      D₁₀ D₃ D₃' h₁₂ h₁₂₃) j hj

theorem degreeTenAndTwoDegreeThreeResidualDatum_cycle_degree
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (hne : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (D₃ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (D₃' : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (h₁₂ : Disjoint (Set.range
      (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
    (h₁₂₃ : Disjoint (Set.range
      (disjointSpecUnionMap
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀)
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃')))
    (j : (degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
      D₁₀ D₃ D₃' h₁₂ h₁₂₃).val.subscheme ⟶
      scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      (degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
        D₁₀ D₃ D₃' h₁₂ h₁₂₃).val.subschemeι)
    [Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))] :
    EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp)
        (degreeTenAndTwoDegreeThreeResidualDatum p q r hp hq hr hne hq0 hrel hregular
          D₁₀ D₃ D₃' h₁₂ h₁₂₃ j hj)) = 11 := by
  exact finiteSubschemeDatumCycle_degree _ _

/-- Starting directly with the degree-ten datum and two degree-three data,
the section-selection and residual construction produce a rank-eleven datum.
The remaining hypotheses are the primeness and transversality assertions for
the selected cubics. -/
theorem exists_degreeTenAndTwoDegreeThreeResidualDatum_of_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (D₃ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (D₃' : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (h₁₂ : Disjoint (Set.range
      (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
    (h₁₂₃ : Disjoint (Set.range
      (disjointSpecUnionMap
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀)
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃')))
    (hprime₁ : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hprime₂ : ∀ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 3 →
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 := by
  let D := degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
    D₁₀ D₃ D₃' h₁₂ h₁₂₃
  let i : D.val.subscheme ⟶ hypersurface p hp := D.val.subschemeι
  haveI : IsClosedImmersion i := by
    dsimp [i]
    infer_instance
  haveI : IsFinite (i ≫ hypersurfaceToBase p hp) := by
    change IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    exact D.property.1
  have hi : finiteSchemeRank (i ≫ hypersurfaceToBase p hp) = 16 := by
    rw [finiteSchemeRank_eq_finrank]
    exact D.property.2.2.2 (IsLocalRing.closedPoint K)
  obtain ⟨q, r, hq, hr, hq0, hrel, hregular, j, hj, hjres⟩ :=
    cubicFiniteSubscheme_degree_sixteen_residual_rank_eleven_of_prime_intermediate
      p hp hne i hi hprime₁ hprime₂ htransverse
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let c := tripleCompleteIntersectionToHypersurface p q r hp hq hr
  let f := hypersurfaceToBase p hp
  letI : IsClosedImmersion j := hj
  letI : IsFinite (toBase I) := triple_cubic_intersection_finite
    p q r hp hq hr hne hq0 hrel hregular
  letI : IsFinite (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    infer_instance
  letI : Etale (c ≫ f) := by
    rw [show c ≫ f = toBase I by
      exact tripleCompleteIntersectionToHypersurface_toBase p q r hp hq hr]
    exact htransverse q r hq hr hq0 hrel hregular
  letI : Etale (toBase I) := htransverse q r hq hr hq0 hrel hregular
  letI : IsFinite (j ≫ toBase I) := by infer_instance
  have hI : finiteSchemeRank (toBase I) = 27 :=
    triple_cubic_intersection_length_twenty_seven p q r hp hq hr hne hq0 hrel hregular
  have hjrank : finiteSchemeRank (j ≫ toBase I) = 16 := by
    let d := finiteSchemeRank (j ≫ toBase I)
    have hcomp := finite_scheme_residual_rank_complement j (toBase I) 27 d hI rfl
      (finiteEtaleScheme_exists_frobeniusFunctional (toBase I))
    rw [hjres] at hcomp
    change d = 16
    omega
  have hX : finiteSchemeRank (c ≫ f) = 27 := by
    simpa only [c, f, tripleCompleteIntersectionToHypersurface_toBase] using hI
  have hZ : finiteSchemeRank (j ≫ c ≫ f) = 16 := by
    simpa only [c, f, Category.assoc,
      tripleCompleteIntersectionToHypersurface_toBase] using hjrank
  refine ⟨finiteSubschemeDatumOfFiniteResidualOnAmbient j c f 27 16 hX hZ
    (finiteEtaleScheme_exists_frobeniusFunctional (c ≫ f)), ?_⟩
  exact finiteSubschemeDatumCycle_degree _ _

/-- Starting with a degree-ten datum on a nonzero prime cubic, the two
successive avoiding line sections supply the degree-sixteen input to the
prime-intermediate residual construction. -/
theorem exists_degreeTenResidualDatum_of_prime_cubic_and_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (hprime₁ : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hprime₂ : ∀ q : MvPolynomial (Fin 4) K, q.IsHomogeneous 3 →
      (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 := by
  obtain ⟨C⟩ := nonempty_degreeTenRankSixteenCompletion_of_prime_cubic
    p hp hne hprime₁ D₁₀
  exact exists_degreeTenAndTwoDegreeThreeResidualDatum_of_prime_intermediate
    p hp hne D₁₀ C.first C.second C.disjoint_first C.disjoint_second
    hprime₁ hprime₂ htransverse

/-- For the degree-ten start, one selected prime intermediate cubic and
transversality suffice for the first residual.  The section-count proof then
selects the third cubic and constructs the rank-eleven residual datum. -/
theorem exists_degreeTenAndTwoDegreeThreeResidualDatum_of_selected_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (D₃ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (D₃' : FiniteSubschemeDatum (hypersurfaceToBase p hp) 3)
    (h₁₂ : Disjoint (Set.range
      (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
    (h₁₂₃ : Disjoint (Set.range
      (disjointSpecUnionMap
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₁₀)
        (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃)))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp) D₃')))
    (hselected : let D := (degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
        D₁₀ D₃ D₃' h₁₂ h₁₂₃)
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell q : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q ≠ 0 ∧ IsRelPrime p q ∧
        (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 := by
  exact exists_finiteSubschemeDatum_degree_sixteen_residual_of_selected_prime_intermediate
    p hp hne (degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
      D₁₀ D₃ D₃' h₁₂ h₁₂₃) hselected htransverse

/-- For a degree-ten datum, primeness is needed only for the surface equation
and for one selected intermediate cubic through the completed degree-sixteen
subscheme. The two disjoint line sections are constructed first; the chosen
prime intermediate and transversality certificate then produce the actual
rank-eleven residual. This removes the stronger and geometrically false
requirement that every cubic through the datum give a prime intersection. -/
theorem exists_degreeTenResidualDatum_of_prime_cubic_and_selected_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hselected : let C : DegreeTenRankSixteenCompletion p hp D₁₀ :=
        Classical.choice (nonempty_degreeTenRankSixteenCompletion_of_prime_cubic p hp hne hprime D₁₀)
      let D := degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
        D₁₀ C.first C.second C.disjoint_first C.disjoint_second
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell q : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q ≠ 0 ∧ IsRelPrime p q ∧
        (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 := by
  let C := Classical.choice
    (nonempty_degreeTenRankSixteenCompletion_of_prime_cubic p hp hne hprime D₁₀)
  exact exists_degreeTenAndTwoDegreeThreeResidualDatum_of_selected_prime_intermediate
    p hp hne D₁₀ C.first C.second C.disjoint_first C.disjoint_second hselected htransverse

/-- The same selected-prime construction retains the finite étaleness of the
rank-eleven residual.  This is the exact finite scheme required as the ambient
input to Voisin's rank-two step. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_of_prime_cubic_and_selected_prime_intermediate
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (hprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (hselected : let C : DegreeTenRankSixteenCompletion p hp D₁₀ :=
        Classical.choice (nonempty_degreeTenRankSixteenCompletion_of_prime_cubic p hp hne hprime D₁₀)
      let D := degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
        D₁₀ C.first C.second C.disjoint_first C.disjoint_second
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell q : MvPolynomial (Fin 4) K),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
        p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q.IsHomogeneous 3 ∧ q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        q ≠ 0 ∧ IsRelPrime p q ∧
        (Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (htransverse : ∀ (q r : MvPolynomial (Fin 4) K)
      (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3),
      q ≠ 0 → IsRelPrime p q →
      (∀ y : MvPolynomial (Fin 4) K,
        r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) →
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  let C := Classical.choice
    (nonempty_degreeTenRankSixteenCompletion_of_prime_cubic p hp hne hprime D₁₀)
  exact
    exists_finiteSubschemeDatum_degree_sixteen_residual_and_toBase_etale_of_selected_prime_intermediate
      p hp hne
      (degreeTenAndTwoDegreeThreeDatum (hypersurfaceToBase p hp)
        D₁₀ C.first C.second C.disjoint_first C.disjoint_second)
      hselected htransverse

/-- The concrete output required from the first Bertini step in Voisin's
degree-ten construction.  It retains the chosen rank-sixteen completion,
both cubics through it, and the one transverse regular triple intersection.
Thus the unresolved geometry is an existence statement for this explicit
scheme-theoretic datum, rather than a universal transversality condition. -/
structure DegreeTenTransverseCubicIntersectionData
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10) where
  completion : DegreeTenRankSixteenCompletion p hp D₁₀
  q : MvPolynomial (Fin 4) K
  r : MvPolynomial (Fin 4) K
  hq : q.IsHomogeneous 3
  hr : r.IsHomogeneous 3
  hrel : IsRelPrime p q
  coordinates :
    let D := completion.datum
    letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
    letI := finiteSchemeCoefficientAlgebra (D.val.subschemeι ≫ hypersurfaceToBase p hp)
    ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤)) (ell : MvPolynomial (Fin 4) K),
      Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
      ell.IsHomogeneous 1 ∧ ell.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 1 ∧
      p.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
      q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
      r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0
  regular : ∀ y : MvPolynomial (Fin 4) K,
    r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
      y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
  transverse : Etale
    (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))

/-- A concrete selected transverse cubic datum gives the finite étale
rank-eleven residual in the first step of Voisin's degree-ten chain. -/
theorem exists_degreeTenResidualDatum_and_toBase_etale_of_transverseCubicIntersectionData
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (T : DegreeTenTransverseCubicIntersectionData p hp D₁₀) :
    ∃ R : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11,
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
        (finiteSubschemeDatumCycle (hypersurfaceToBase p hp) R) = 11 ∧
      Etale (R.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  obtain ⟨x, ell, hxsurj, hell, hxell, hpx, hqvan, hrvan⟩ := T.coordinates
  exact
    exists_degreeTenResidualDatum_and_toBase_etale_of_completion_and_selected_regular_transverse_cubic
      p T.q hp T.hq hne T.hrel D₁₀ T.completion
      ⟨x, ell, T.r, T.hr, hxsurj, hell, hxell, hpx, hqvan, hrvan,
        T.regular, T.transverse⟩

/-- The rank-eleven residual selected by a concrete transverse three-cubic
datum.  Naming this choice lets the subsequent rank-two pencil be stated
with the actual residual endpoint, instead of an existential placeholder. -/
noncomputable def degreeTenResidualDatumOfTransverseCubicIntersectionData
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (T : DegreeTenTransverseCubicIntersectionData p hp D₁₀) :
    FiniteSubschemeDatum (hypersurfaceToBase p hp) 11 :=
  Classical.choose
    (exists_degreeTenResidualDatum_and_toBase_etale_of_transverseCubicIntersectionData
      p hp hne D₁₀ T)

/-- The selected rank-eleven residual has its expected degree. -/
theorem degreeTenResidualDatumOfTransverseCubicIntersectionData_cycle_degree
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (T : DegreeTenTransverseCubicIntersectionData p hp D₁₀) :
    EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp)
        (degreeTenResidualDatumOfTransverseCubicIntersectionData p hp hne D₁₀ T)) = 11 := by
  exact (Classical.choose_spec
    (exists_degreeTenResidualDatum_and_toBase_etale_of_transverseCubicIntersectionData
      p hp hne D₁₀ T)).1

/-- The selected rank-eleven residual is finite étale over the ground field. -/
theorem degreeTenResidualDatumOfTransverseCubicIntersectionData_toBase_etale
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (T : DegreeTenTransverseCubicIntersectionData p hp D₁₀) :
    Etale
      ((degreeTenResidualDatumOfTransverseCubicIntersectionData p hp hne D₁₀ T).val.subschemeι ≫
        hypersurfaceToBase p hp) := by
  exact (Classical.choose_spec
    (exists_degreeTenResidualDatum_and_toBase_etale_of_transverseCubicIntersectionData
      p hp hne D₁₀ T)).2

/-- A first residual datum with its actual containment in the chosen
three-cubic complete intersection.  The coordinate-only selector records
the numerical residual calculation, but this stronger datum is what connects
that calculation to the completed degree-ten subscheme and hence to the
first finite-flat pencil. -/
structure DegreeTenTransverseCubicIntersectionEmbeddingData
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10) where
  completion : DegreeTenRankSixteenCompletion p hp D₁₀
  q : MvPolynomial (Fin 4) K
  r : MvPolynomial (Fin 4) K
  hq : q.IsHomogeneous 3
  hr : r.IsHomogeneous 3
  hrel : IsRelPrime p q
  regular : ∀ y : MvPolynomial (Fin 4) K,
    r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
      y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))
  embedding : completion.datum.val.subscheme ⟶
    scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)
  embedding_closed : IsClosedImmersion embedding
  embedding_over : embedding ≫
      tripleCompleteIntersectionToHypersurface p q r hp hq hr =
    completion.datum.val.subschemeι
  transverse : Etale
    (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))

/-- Build the first embedded-intersection datum from any isomorphic
presentation of the completed rank-sixteen scheme.  This is the form in
which projective-chart and Hilbert-scheme constructions naturally provide
the containment: the presentation map is preserved all the way to the
canonical finite-subscheme datum. -/
noncomputable def DegreeTenTransverseCubicIntersectionEmbeddingData.ofPresentation
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    {Z : Scheme.{u}} (e : Z ≅ C.datum.val.subscheme)
    (j : Z ⟶ scheme (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))
    [IsClosedImmersion j]
    (hj : j ≫ tripleCompleteIntersectionToHypersurface p q r hp hq hr =
      e.hom ≫ C.datum.val.subschemeι)
    (htransverse : Etale
      (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ) :
    DegreeTenTransverseCubicIntersectionEmbeddingData p hp D₁₀ :=
  { completion := C
    q := q
    r := r
    hq := hq
    hr := hr
    hrel := hrel
    regular := hregular
    embedding := finiteSubschemeDatumCompleteIntersectionEmbeddingOfIso
      p q r hp hq hr 16 C.datum e j
    embedding_closed := by infer_instance
    embedding_over := finiteSubschemeDatumCompleteIntersectionEmbeddingOfIso_fac
      p q r hp hq hr 16 C.datum e j hj
    transverse := htransverse }

/-- The same first-residual datum can be formed directly from the kernel
inclusion saying that the chosen two cubics vanish on the completed datum.
This is the intrinsic endpoint of the remaining projective containment
argument. -/
noncomputable def DegreeTenTransverseCubicIntersectionEmbeddingData.ofKernelLe
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (hker : (tripleCompleteIntersectionToHypersurface p q r hp hq hr).ker ≤
      C.datum.val.subschemeι.ker)
    (htransverse : Etale
      (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ) :
    DegreeTenTransverseCubicIntersectionEmbeddingData p hp D₁₀ :=
  { completion := C
    q := q
    r := r
    hq := hq
    hr := hr
    hrel := hrel
    regular := hregular
    embedding := tripleCompleteIntersectionLift
      p q r hp hq hr C.datum.val.subschemeι hker
    embedding_closed := by infer_instance
    embedding_over := tripleCompleteIntersectionLift_fac
      p q r hp hq hr C.datum.val.subschemeι hker
    transverse := htransverse }

/-- Build the first embedded-intersection datum from the normalized chart of
the actual completed finite subscheme.  The two selected cubics are required
to vanish on that chart, so the resulting complete-intersection map is proved
to recover the original finite-subscheme immersion, not merely its structure
map to the ground field. -/
noncomputable def DegreeTenTransverseCubicIntersectionEmbeddingData.ofNormalizedChart
    [CharZero K]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (C : DegreeTenRankSixteenCompletion p hp D₁₀)
    (hrel : IsRelPrime p q)
    (hregular : ∀ y : MvPolynomial (Fin 4) K,
      r * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (chart : let D := C.datum
      letI : IsFinite (D.val.subschemeι ≫ hypersurfaceToBase p hp) := D.property.1
      letI : IsAffine D.val.subscheme :=
        isAffine_of_isAffineHom (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      letI := finiteSchemeCoefficientAlgebra
        (D.val.subschemeι ≫ hypersurfaceToBase p hp)
      ∃ (z : CoordinateRing (equationIdeal p hp))
        (hz : z ∈ grading (equationIdeal p hp) 1)
        (x : Fin 4 → Γ(D.val.subscheme, ⊤))
        (he : ∀ s ∈ (equationIdeal p hp).toIdeal,
          (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) s = 0)
        (hzOne : (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
          (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) he) z = 1),
        Function.Surjective (eval₂Hom (algebraMap K Γ(D.val.subscheme, ⊤)) x) ∧
        q.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        r.eval₂ (algebraMap K Γ(D.val.subscheme, ⊤)) x = 0 ∧
        linearNormalizedPointAt (equationIdeal p hp) x he z hz hzOne =
          D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι)
    (htransverse : Etale
      (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr)) ) :
    DegreeTenTransverseCubicIntersectionEmbeddingData p hp D₁₀ := by
  exact
    { completion := C
      q := q
      r := r
      hq := hq
      hr := hr
      hrel := hrel
      regular := hregular
      embedding := finiteSubschemeDatumCompleteIntersectionEmbeddingOfNormalizedChart
        p q r hp hq hr 16 C.datum chart
      embedding_closed :=
        finiteSubschemeDatumCompleteIntersectionEmbeddingOfNormalizedChart_isClosedImmersion
          p q r hp hq hr 16 C.datum chart
      embedding_over :=
        finiteSubschemeDatumCompleteIntersectionEmbeddingOfNormalizedChart_fac
          p q r hp hq hr 16 C.datum chart
      transverse := htransverse }

/-- The actual rank-eleven residual defined by a transverse first
complete-intersection embedding. -/
noncomputable def degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (T : DegreeTenTransverseCubicIntersectionEmbeddingData p hp D₁₀) :
    FiniteSubschemeDatum (hypersurfaceToBase p hp) 11 := by
  letI : IsClosedImmersion T.embedding := T.embedding_closed
  letI : Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p T.q T.r hp T.hq T.hr)) := T.transverse
  exact finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding
    p T.q T.r hp T.hq T.hr hne
    (isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hp (by decide) T.hrel)
    T.hrel T.regular T.completion.datum T.embedding T.embedding_over

/-- The first embedded residual has degree eleven. -/
theorem degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData_cycle_degree
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (T : DegreeTenTransverseCubicIntersectionEmbeddingData p hp D₁₀) :
    EffectiveZeroCycle.degree (hypersurfaceToBase p hp)
      (finiteSubschemeDatumCycle (hypersurfaceToBase p hp)
        (degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData
          p hp hne D₁₀ T)) = 11 :=
  finiteSubschemeDatumCycle_degree _ _

/-- The actual first embedded residual remains finite étale over the ground
field, as required for the rank-two construction. -/
theorem degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData_toBase_etale
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (T : DegreeTenTransverseCubicIntersectionEmbeddingData p hp D₁₀) :
    Etale
      ((degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData
        p hp hne D₁₀ T).val.subschemeι ≫ hypersurfaceToBase p hp) := by
  letI : IsClosedImmersion T.embedding := T.embedding_closed
  letI : Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p T.q T.r hp T.hq T.hr)) := T.transverse
  exact finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding_toBase_etale
    p T.q T.r hp T.hq T.hr hne
    (isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hp (by decide) T.hrel)
    T.hrel T.regular T.completion.datum T.embedding T.embedding_over

/-- The first embedded residual is disjoint from the degree-ten completion.
This supplies the support condition of Voisin's first pencil from the
complete-intersection geometry. -/
theorem degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData_disjoint
    [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (D₁₀ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 10)
    (T : DegreeTenTransverseCubicIntersectionEmbeddingData p hp D₁₀) :
    Disjoint
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp)
        T.completion.datum))
      (Set.range (finiteSubschemeDatumSpecMap (hypersurfaceToBase p hp)
        (degreeTenResidualDatumOfTransverseCubicIntersectionEmbeddingData
          p hp hne D₁₀ T))) := by
  letI : IsClosedImmersion T.embedding := T.embedding_closed
  letI : Etale (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p T.q T.r hp T.hq T.hr)) := T.transverse
  exact (disjoint_finiteSubschemeDatum_degree_sixteen_residual_of_completeIntersectionEmbedding
    p T.q T.r hp T.hq T.hr hne
    (isRelPrime_right_ne_zero_of_left_homogeneous_pos_degree hp (by decide) T.hrel)
    T.hrel T.regular T.completion.datum T.embedding T.embedding_over).symm

end PfaffianDescent
