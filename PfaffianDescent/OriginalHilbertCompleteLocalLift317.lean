import PfaffianDescent.OriginalCoefficientProjectiveFamily317
import PfaffianDescent.MonomialPolynomialLocusSmoothOpen312
import AllCharacteristics.SmoothAlgebraPointLifting
import AllCharacteristics.FieldParameterResidue
import PfaffianDescent.NativeOriginalClosedPointFibre317
import PfaffianDescent.OriginalClosedPointCoefficientSmooth317

/-! SOURCE ONLY317. The actual local Hilbert smooth point lifts its classifier
over a complete local base. The inverse representing family, followed by the
original projective chart embedding, retains the exact original point fibre.
Pending prerequisite: the original closed-point smooth membership producer. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Complete-local lifting at an ACTUAL native smooth-locus point.
This builds the morphism internally from accepted smooth-on-smooth-locus and
complete-local smooth-point lifting; no section or Henselian lift is assumed. -/
private theorem hilbertSmoothLocus_completeLocalPointLift317
    {R A K : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] [Field K]
    {X : Scheme.{u}} (F : X ⟶ Spec (.of R)) [LocallyOfFinitePresentation F]
    (b : A →+* K) (hb : Function.Surjective b)
    (q : Spec (.of K) ⟶ X)
    (hq : q ≫ F = Spec.map (CommRingCat.ofHom (b.comp (algebraMap R A))))
    (hsm : q (IsLocalRing.closedPoint K) ∈ F.smoothLocus) :
    ∃ s : Spec (.of A) ⟶ X,
      s ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
      Spec.map (CommRingCat.ofHom b) ≫ s = q := by
  have hrange : Set.range q ⊆ Set.range F.smoothLocus.ι := by
    rw [F.smoothLocus.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    change q x ∈ F.smoothLocus
    rw [hx]
    exact hsm
  let qU := IsOpenImmersion.lift F.smoothLocus.ι q hrange
  have hqU : qU ≫ (F.smoothLocus.ι ≫ F) =
      Spec.map (CommRingCat.ofHom (b.comp (algebraMap R A))) := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, hq]
  letI : Smooth (F.smoothLocus.ι ≫ F) := AllCharacteristics.smooth_on_smoothLocus F
  obtain ⟨s, hs, hred⟩ := AllCharacteristics.lift_smooth_point_to_complete_local_algebra
    (F.smoothLocus.ι ≫ F) b hb qU hqU
  refine ⟨s ≫ F.smoothLocus.ι, ?_, ?_⟩
  · simpa only [Category.assoc] using hs
  · rw [← Category.assoc, hred]
    exact IsOpenImmersion.lift_fac _ _ _

/-- The actual field-valued coefficient point has the original kernel prime. -/
private lemma hilbertCoefficientFieldPoint_eq_kernel317
    {C K : Type u} [CommRing C] [Field K] (k : C →+* K)
    (q : PrimeSpectrum C) (hq : q.asIdeal = RingHom.ker k) :
    Spec.map (CommRingCat.ofHom k) (IsLocalRing.closedPoint K) = q := by
  apply PrimeSpectrum.ext
  change (PrimeSpectrum.comap k (IsLocalRing.closedPoint K)).asIdeal = q.asIdeal
  exact (AllCharacteristics.fieldPoint_asIdeal_eq_ker k).trans hq.symm

/-- A smooth ACTUAL coefficient point constructs a lifted classifier on
the SAME original-ground polynomial Hilbert locus. This internal bridge takes
membership honestly; the original closed-point caller derives it separately. -/
lemma originalHilbertCoefficientSmoothPoint_classifierLift317
    (R : Type u) [CommRing R] {A K : Type u} [CommRing A] [Algebra R A]
    [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] [Field K] [Algebra R K]
    (b : A →ₐ[R] K) (hb : Function.Surjective b)
    (m n : ℕ) (p : MvPolynomial (Fin m) R)
    (i : MonomialCoefficientChartIndex300 m n)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i →ₐ[R] K)
    (q₀ : PrimeSpectrum (MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i))
    (hq₀ : q₀.asIdeal = RingHom.ker k.toRingHom)
    (hsm : monomialClosedCoefficientChartToLocus312 R m n p i q₀ ∈
      monomialPolynomialContainmentSmoothOpen312 R m n p) :
    ∃ c : originalNormalizedAffineTest317 R A ⟶
        monomialPolynomialContainmentRepresentingObject312 R m n p,
      originalNormalizedAffineTestMap317 R b ≫ c =
        originalCoefficientTestClassifyingMap317 R m n p i k := by
  let F := (monomialPolynomialContainmentRepresentingObject312 R m n p).hom
  let q := (originalCoefficientTestClassifyingMap317 R m n p i k).left
  letI : LocallyOfFinitePresentation F :=
    monomialPolynomialContainmentLocusToBase_locallyOfFinitePresentation312 R m n p
  have hscalar : b.toRingHom.comp (algebraMap R A) = algebraMap R K := by
    ext r
    exact b.commutes r
  have hq : q ≫ F = Spec.map (CommRingCat.ofHom (b.toRingHom.comp (algebraMap R A))) := by
    have hw := (originalCoefficientTestClassifyingMap317 R m n p i k).w
    change q ≫ F = Spec.map (CommRingCat.ofHom (algebraMap R K)) at hw
    exact hw.trans (congrArg (fun a : R →+* K => Spec.map (CommRingCat.ofHom a)) hscalar).symm
  have hmem : q (IsLocalRing.closedPoint K) ∈ F.smoothLocus := by
    change monomialClosedCoefficientChartToLocus312 R m n p i
        (Spec.map (CommRingCat.ofHom k.toRingHom) (IsLocalRing.closedPoint K)) ∈
      monomialPolynomialContainmentSmoothOpen312 R m n p
    rw [hilbertCoefficientFieldPoint_eq_kernel317 k.toRingHom q₀ hq₀]
    exact hsm
  obtain ⟨s, hs, hred⟩ := hilbertSmoothLocus_completeLocalPointLift317 F b.toRingHom hb q hq hmem
  refine ⟨Over.homMk s hs, ?_⟩
  apply Over.OverMorphism.ext
  exact hred

/-- A literal rank-n projective whole family reducing to the ORIGINAL P.
The residue equation and reduction map are the actual original R-algebra maps. -/
def OriginalHilbertProjectiveFieldLift317
    (R : Type u) [CommRing R] {A K : Type u} [CommRing A] [Algebra R A]
    [Field K] [Algebra R K] (b : A →ₐ[R] K)
    (r : MvPolynomial (Fin 4) R) {d : ℕ} (hr : r.IsHomogeneous d) (n : ℕ)
    (P : closedPoints (hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K)))) : Prop :=
  ∃ Q : FiniteFlatHilbertPoint195
      (hypersurfaceToBase (r.map (algebraMap R A)) (hr.map (algebraMap R A))) n,
    Q.val.comap (hypersurfaceReductionMap b.toRingHom
      (r.map (algebraMap R A)) (hr.map (algebraMap R A))
      (r.map (algebraMap R K)) (hr.map (algebraMap R K))
      (originalNormalizedTestEquation317 R b r)) =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker

/-- The ACTUAL smooth Hilbert classifier produces its universal physical
family and pushes it through the ORIGINAL projective chart. The projective
family and exact reduction are derived; global projective-Hilbert gluing is
not supplied or asserted. This internal bridge's field identity/membership
inputs are proved by the original closed-point caller. -/
lemma originalHilbertCoefficientSmoothPoint_projectiveLift317
    (R : Type u) [CommRing R] {A K : Type u} [CommRing A] [Algebra R A]
    [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A] [Field K] [Algebra R K]
    (b : A →ₐ[R] K) (hb : Function.Surjective b)
    (r : MvPolynomial (Fin 4) R) {d : ℕ} (hr : r.IsHomogeneous d)
    (n : ℕ) (hn : 0 < n)
    (P : closedPoints (hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))))
    (j : Fin 4) (i : MonomialCoefficientChartIndex300 3 n)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
      (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R n r hr j hn i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    (q₀ : PrimeSpectrum (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 n
      (originalNormalizedHypersurfacePolynomial312 r j) i))
    (hq₀ : q₀.asIdeal = RingHom.ker k.toRingHom)
    (hsm : monomialClosedCoefficientChartToLocus312 R 3 n
        (originalNormalizedHypersurfacePolynomial312 r j) i q₀ ∈
      monomialPolynomialContainmentSmoothOpen312 R 3 n
        (originalNormalizedHypersurfacePolynomial312 r j)) :
    OriginalHilbertProjectiveFieldLift317 R b r hr n P := by
  obtain ⟨c, hc⟩ := originalHilbertCoefficientSmoothPoint_classifierLift317 R b hb
    3 n (originalNormalizedHypersurfacePolynomial312 r j) i k q₀ hq₀ hsm
  let Q := originalNormalizedAffinePointOfClassifier317 R r hr j A n hn c
  have hQ : originalNormalizedAffinePointReduction317 R b r hr j n Q =
      originalCoefficientTestPhysicalFamily317 R n r hr j hn i k :=
    (originalNormalizedAffinePointOfClassifier_natural317 R r hr j n hn b c).trans
      (congrArg (originalNormalizedAffinePointOfClassifier317 R r hr j K n hn) hc)
  let Z := originalNormalizedAffinePointToProjective317
    (r.map (algebraMap R A)) (hr.map (algebraMap R A)) j n Q
  have hred := originalNormalizedAffinePointToProjective_reductionWholeIdeal317
    (r.map (algebraMap R A)) (hr.map (algebraMap R A)) j n Q b.toRingHom
    (r.map (algebraMap R K)) (hr.map (algebraMap R K))
    (originalNormalizedTestEquation317 R b r)
  change (originalNormalizedAffinePointToProjective317
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j n
      (originalNormalizedAffinePointReduction317 R b r hr j n Q)).val =
    Z.val.comap (hypersurfaceReductionMap b.toRingHom
      (r.map (algebraMap R A)) (hr.map (algebraMap R A))
      (r.map (algebraMap R K)) (hr.map (algebraMap R K))
      (originalNormalizedTestEquation317 R b r)) at hred
  have hleft := congrArg (fun W => (originalNormalizedAffinePointToProjective317
    (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j n W).val) hQ
  exact ⟨Z, hred.symm.trans (hleft.trans hpoint)⟩

section OriginalPoint
variable (R : Type u) [CommRing R] (r : MvPolynomial (Fin 4) R)
  (hr : r.IsHomogeneous 3) (K : Type u) [Field K] [Algebra R K]
  (P : closedPoints (hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))))
local notation "pointDegree" => Scheme.Hom.residueDegree
  (hypersurfaceToBase (r.map (algebraMap R K)) (hr.map (algebraMap R K))) P.val

/-- ORIGINAL smooth cubic/closed point → actual finite-flat projective family
over the SPECIFIED complete local coefficient algebra, with ORIGINAL P as its
whole special fibre. No chart/membership/classifier/lift/family outcome input.
The original-point smooth membership theorem is the pending prerequisite. -/
lemma originalClosedPoint_hilbertProjectiveLift_completeAlgebra317
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (hRK : Function.Surjective (algebraMap R K))
    {A : Type u} [CommRing A] [Algebra R A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (b : A →ₐ[R] K)
    (hb : Function.Surjective b) :
    OriginalHilbertProjectiveFieldLift317 R b r hr pointDegree P := by
  obtain ⟨j, i, k, hk, hpoint, q₀, hq₀, hsm⟩ :=
    originalClosedPoint_coefficientChart_memSmooth_exists317 R r hr K P hK0 hRK
  exact originalHilbertCoefficientSmoothPoint_projectiveLift317 R b hb r hr pointDegree
    (originalClosedPoint_residueDegree_pos317 R r hr K P) P j i k hpoint q₀ hq₀ hsm

/-- The SAME original projective hypersurface over R, with no self-map alias
in the result. This is the literal geometric finite-flat lifting target once
the smooth original cubic and its complete local base have been constructed. -/
def OriginalGroundHilbertClosedPointLift317 : Prop :=
  ∃ Q : FiniteFlatHilbertPoint195 (hypersurfaceToBase r hr) pointDegree,
    Q.val.comap (hypersurfaceReductionMap (algebraMap R K) r hr
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) rfl) =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker

/-- ORIGINAL complete local ground base receives the Hilbert universal whole
family of exact original point degree. The native smooth coefficient point,
complete-local classifier section and universal family are all constructed. -/
lemma originalClosedPoint_hilbertProjectiveLift317
    [IsNoetherianRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (hRK : Function.Surjective (algebraMap R K)) :
    OriginalGroundHilbertClosedPointLift317 R r hr K P := by
  let b : R →ₐ[R] K := Algebra.ofId R K
  have h := originalClosedPoint_hilbertProjectiveLift_completeAlgebra317
    R r hr K P hK0 hRK b hRK
  have transport : ∀ (p : MvPolynomial (Fin 4) R) (hp : p.IsHomogeneous 3)
      (he : p.map (algebraMap R K) = r.map (algebraMap R K)), p = r →
      (∃ Q : FiniteFlatHilbertPoint195 (hypersurfaceToBase p hp) pointDegree,
        Q.val.comap (hypersurfaceReductionMap (algebraMap R K) p hp
          (r.map (algebraMap R K)) (hr.map (algebraMap R K)) he) =
          ((hypersurface (r.map (algebraMap R K))
            (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker) →
      OriginalGroundHilbertClosedPointLift317 R r hr K P := by
    intro p hp he ep hQ
    subst p
    exact hQ
  exact transport (r.map (algebraMap R R)) (hr.map (algebraMap R R))
    (originalNormalizedTestEquation317 R b r)
    (by simp only [Algebra.algebraMap_self, MvPolynomial.map_id]) h

/-- Literal embedded Section5 family and ORIGINAL single-point special-fibre
Cartesian square, extracted from the constructed Hilbert whole family.
No DVR/coefficient family-lifting alternative is called in this proof. -/
lemma originalClosedPoint_hilbertFiniteFlatClosedSubscheme317
    [IsNoetherianRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (hRK : Function.Surjective (algebraMap R K)) :
    ∃ (Z : Scheme.{u}) (a : Z ⟶ hypersurface r hr)
      (u0 : Spec ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).residueField P.val) ⟶ Z),
      IsClosedImmersion a ∧ IsFinite (a ≫ hypersurfaceToBase r hr) ∧
      Flat (a ≫ hypersurfaceToBase r hr) ∧
      (∀ y, (a ≫ hypersurfaceToBase r hr).finrank y = pointDegree) ∧
      IsPullback u0
        ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val)
        a (hypersurfaceReductionMap (algebraMap R K) r hr
          (r.map (algebraMap R K)) (hr.map (algebraMap R K)) rfl) := by
  obtain ⟨Q, hQ⟩ := originalClosedPoint_hilbertProjectiveLift317 R r hr K P hK0 hRK
  let d := hypersurfaceReductionMap (algebraMap R K) r hr
    (r.map (algebraMap R K)) (hr.map (algebraMap R K)) rfl
  exact ⟨Q.val.subscheme, Q.val.subschemeι,
    nativeOriginalClosedPointFibreMap317 Q.val d P hQ,
    inferInstance, Q.property.1, Q.property.2.1, Q.property.2.2,
    nativeOriginalClosedPointFibreMap_isPullback317 Q.val d P hQ⟩
end OriginalPoint

end PfaffianDescent
end
