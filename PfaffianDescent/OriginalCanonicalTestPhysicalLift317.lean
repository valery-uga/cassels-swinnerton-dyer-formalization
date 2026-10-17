import PfaffianDescent.OriginalCanonicalNativeTestLiftCuts317

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] canonicalOriginalChartOpen317

/-- Every ORIGINAL projective hypersurface point has an actual normalized
chart, from the accepted coordinate cover and the constructed312 chart Iso. -/
lemma originalNormalizedHypersurfaceChart_exists317
    {A : Type u} [CommRing A] (p : MvPolynomial (Fin 4) A)
    {d : ℕ} (hp : p.IsHomogeneous d) (x : hypersurface p hp) :
    ∃ j : Fin 4, x ∈ (originalNormalizedHypersurfaceChartEmbedding312 p hp j).opensRange := by
  obtain ⟨j, y, hy⟩ := exists_coordinate_chart (equationIdeal p hp) x
  let e := originalNormalizedHypersurfaceChartSpecIso312 p hp j
  refine ⟨j, e.inv y, ?_⟩
  change (e.hom ≫ chartι (equationIdeal p hp) j) (e.inv y) = x
  exact (congrArg (fun t : Spec (.of (ChartRing (equationIdeal p hp) j)) ⟶
    hypersurface p hp => t y) (e.inv_hom_id_assoc (chartι (equationIdeal p hp) j))).trans hy

section OriginalCanonicalPoint
variable (R : Type u) [CommRing R] (r : MvPolynomial (Fin 4) R)
variable (hr : r.IsHomogeneous 3) (K : Type u) [Field K] [Algebra R K]
variable (P : closedPoints (hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))))
local notation "pointDegree" => Scheme.Hom.residueDegree (hypersurfaceToBase (r.map (algebraMap R K))
  (hr.map (algebraMap R K))) P.val
local notation "pointPositive" => originalClosedPoint_residueDegree_pos317 R r hr K P

/-- Bounded original composition diagnostic013: capture ONLY the original physical-transport factory before supplying a Q. All actual maps retained; no desired outcome input. -/
private def originalActualPhysicalTransportFactory013
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  originalCanonicalNativeWholeIdealPhysicalReduction317 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN

/-- Bounded original composition diagnostic013: capture the passed exact native Q existential application without destructuring. All actual maps retained; no desired outcome input. -/
private def originalActualNativeWholeQPackage013
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  originalCanonicalNativeWholeChartQ317 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN

/-- Bounded original composition diagnostic013: choose the genuine actual normalized finiteflat Q from that existential. All actual maps retained; no desired outcome input. -/
private def originalActualNativeWholeQChoice013
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  Classical.choose (originalActualNativeWholeQPackage013 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN)

/-- Bounded original composition diagnostic013: retain its exact native original whole-comap certificate. All actual maps retained; no desired outcome input. -/
private def originalActualNativeWholeQCertificate013
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  Classical.choose_spec (originalActualNativeWholeQPackage013 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN)

/-- Bounded original composition diagnostic013: apply original physical-transport factory to ONLY the genuine actual Q; native equality remains an argument. All actual maps retained; no desired outcome input. -/
private def originalActualPhysicalTransportSuppliedQ013
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  originalActualPhysicalTransportFactory013 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
    (originalActualNativeWholeQChoice013 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN)

/-- Bounded original composition diagnostic013: supply the genuine exact native whole-comap certificate and infer actual physical equality. All actual maps retained; no desired outcome input. -/
private def originalActualPhysicalTransportSuppliedCertificate013
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N) :=
  originalActualPhysicalTransportSuppliedQ013 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN
    (originalActualNativeWholeQCertificate013 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN)

/-- ORIGINAL degree canonical physical-test property. Its genuine Q is
constructed by the bounded whole-chart producer, then transported by the
independent whole-ideal/physical reduction cut. No Q or reduction premise. -/
private theorem originalCanonicalPolynomialPhysicalTests317
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (j : Fin 4)
    (hP : P.val ∈ (originalNormalizedHypersurfaceChartEmbedding312
      (r.map (algebraMap R K)) (hr.map (algebraMap R K)) j).opensRange)
    (i : MonomialCoefficientChartIndex300 3 pointDegree)
    (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k)
    (hpoint : (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
      ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker)
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
    (hq : RingHom.ker k.toRingHom = q) :
    OriginalPolynomialPhysicalTestLifts317 R pointDegree r hr j pointPositive i f hf q := by
  intro N hN
  exact ⟨originalActualNativeWholeQChoice013 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN,
    originalActualPhysicalTransportSuppliedCertificate013 R r hr K P hK0 j hP i k hk hpoint f hf q hq N hN⟩

/-- Bounded ORIGINAL point specialization018: capture actual original chart-cover existence at SAME P. No derived geometry/lift outcome is an input. -/
private def originalActualClosedPointChartPackage018 :=
  originalNormalizedHypersurfaceChart_exists317 (r.map (algebraMap R K)) (hr.map (algebraMap R K)) P.val

/-- Bounded ORIGINAL point specialization018: choose actual chart j from that proved cover. No derived geometry/lift outcome is an input. -/
private def originalActualClosedPointChartChoice018 :=
  Classical.choose (originalActualClosedPointChartPackage018 R r hr K P)

/-- Bounded ORIGINAL point specialization018: derive SAME original P membership in chosen chart. No derived geometry/lift outcome is an input. -/
private def originalActualClosedPointChartMembership018 :=
  Classical.choose_spec (originalActualClosedPointChartPackage018 R r hr K P)

/-- Bounded ORIGINAL point specialization018: apply actual coefficient existence to original P and derived chart/membership. No derived geometry/lift outcome is an input. -/
private def originalActualClosedPointCoefficientPackage018
    (hRK : Function.Surjective (algebraMap R K)) :=
  originalClosedPoint_surjectiveCoefficientChart_exists317 R r hr K P
    (originalActualClosedPointChartChoice018 R r hr K P) (originalActualClosedPointChartMembership018 R r hr K P) hRK

/-- Bounded ORIGINAL point specialization018: choose coefficient index at ORIGINAL P residue degree. No derived geometry/lift outcome is an input. -/
private def originalActualClosedPointCoefficientIndex018
    (hRK : Function.Surjective (algebraMap R K)) :=
  Classical.choose (originalActualClosedPointCoefficientPackage018 R r hr K P hRK)

/-- Bounded ORIGINAL point specialization018: retain actual existence of field map on SAME chosen coefficient index. No derived geometry/lift outcome is an input. -/
private def originalActualClosedPointCoefficientMapPackage018
    (hRK : Function.Surjective (algebraMap R K)) :=
  Classical.choose_spec (originalActualClosedPointCoefficientPackage018 R r hr K P hRK)

/-- Bounded ORIGINAL point specialization018: choose actual coefficient AlgHom into SAME original K. No derived geometry/lift outcome is an input. -/
private def originalActualClosedPointCoefficientMap018
    (hRK : Function.Surjective (algebraMap R K)) :=
  Classical.choose (originalActualClosedPointCoefficientMapPackage018 R r hr K P hRK)

/-- Bounded ORIGINAL point specialization018: retain native conjunction of field-map surjectivity and fieldfamily=P whole kernel. No derived geometry/lift outcome is an input. -/
private def originalActualClosedPointCoefficientMapFacts018
    (hRK : Function.Surjective (algebraMap R K)) :=
  Classical.choose_spec (originalActualClosedPointCoefficientMapPackage018 R r hr K P hRK)

/-- Bounded ORIGINAL point specialization018: derive surjectivity of SAME chosen original coefficient field map. No derived geometry/lift outcome is an input. -/
private def originalActualClosedPointCoefficientSurjective018
    (hRK : Function.Surjective (algebraMap R K)) :=
  (originalActualClosedPointCoefficientMapFacts018 R r hr K P hRK).1

/-- Bounded ORIGINAL point specialization018: derive original actual projective field-family equals P WHOLE kernel. No derived geometry/lift outcome is an input. -/
private def originalActualClosedPointCoefficientWholeIdeal018
    (hRK : Function.Surjective (algebraMap R K)) :=
  (originalActualClosedPointCoefficientMapFacts018 R r hr K P hRK).2

/-- Bounded ORIGINAL point specialization018: capture passed named all-test producer before original chosen chart arguments. No derived geometry/lift outcome is an input. -/
private def originalActualClosedPointPhysicalFactoryBase018
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (hRK : Function.Surjective (algebraMap R K)) :=
  originalCanonicalPolynomialPhysicalTests317 R r hr K P hK0

/-- Bounded ORIGINAL point specialization018: supply ONLY derived original chart j. No derived geometry/lift outcome is an input. -/
private def originalActualClosedPointPhysicalFactoryChart018
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (hRK : Function.Surjective (algebraMap R K)) :=
  originalActualClosedPointPhysicalFactoryBase018 R r hr K P hK0 hRK
    (originalActualClosedPointChartChoice018 R r hr K P)

/-- Bounded ORIGINAL point specialization018: supply ONLY its derived original P chart membership. No derived geometry/lift outcome is an input. -/
private def originalActualClosedPointPhysicalFactoryMembership018
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (hRK : Function.Surjective (algebraMap R K)) :=
  originalActualClosedPointPhysicalFactoryChart018 R r hr K P hK0 hRK
    (originalActualClosedPointChartMembership018 R r hr K P)

/-- Bounded ORIGINAL point specialization018: supply ONLY chosen actual coefficient index at original P degree. No derived geometry/lift outcome is an input. -/
private def originalActualClosedPointPhysicalFactoryIndex018
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (hRK : Function.Surjective (algebraMap R K)) :=
  originalActualClosedPointPhysicalFactoryMembership018 R r hr K P hK0 hRK
    (originalActualClosedPointCoefficientIndex018 R r hr K P hRK)

/-- Bounded ORIGINAL point specialization018: supply ONLY chosen actual coefficient-to-original-field AlgHom. No derived geometry/lift outcome is an input. -/
private def originalActualClosedPointPhysicalFactoryFieldMap018
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (hRK : Function.Surjective (algebraMap R K)) :=
  originalActualClosedPointPhysicalFactoryIndex018 R r hr K P hK0 hRK
    (originalActualClosedPointCoefficientMap018 R r hr K P hRK)

/-- Bounded ORIGINAL point specialization018: supply ONLY internally derived chosen field-map surjectivity. No derived geometry/lift outcome is an input. -/
private def originalActualClosedPointPhysicalFactorySurjective018
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (hRK : Function.Surjective (algebraMap R K)) :=
  originalActualClosedPointPhysicalFactoryFieldMap018 R r hr K P hK0 hRK
    (originalActualClosedPointCoefficientSurjective018 R r hr K P hRK)

/-- Bounded ORIGINAL point specialization018: supply ONLY internally derived exact chosen field-family=P whole-kernel identity. No derived geometry/lift outcome is an input. -/
private def originalActualClosedPointPhysicalFactoryWholeIdeal018
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (hRK : Function.Surjective (algebraMap R K)) {v : ℕ} :=
  originalActualClosedPointPhysicalFactorySurjective018 R r hr K P hK0 hRK
    (originalActualClosedPointCoefficientWholeIdeal018 R r hr K P hRK) (v := v)

/-- Bounded ORIGINAL point specialization018: apply original presentation/kernel-prime arguments to derived named all-positiveN property. No derived geometry/lift outcome is an input. -/
private def originalActualClosedPointPhysicalPresentation018
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (hRK : Function.Surjective (algebraMap R K))
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree
      (originalNormalizedHypersurfacePolynomial312 r (originalActualClosedPointChartChoice018 R r hr K P)) (originalActualClosedPointCoefficientIndex018 R r hr K P hRK))
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree
      (originalNormalizedHypersurfacePolynomial312 r (originalActualClosedPointChartChoice018 R r hr K P)) (originalActualClosedPointCoefficientIndex018 R r hr K P hRK))) [q.IsPrime]
    (hq : RingHom.ker (originalActualClosedPointCoefficientMap018 R r hr K P hRK).toRingHom = q) :=
  originalActualClosedPointPhysicalFactoryWholeIdeal018 R r hr K P hK0 hRK (v := v) f hf q hq

/-- Bounded ORIGINAL point specialization018: supply ONLY positive N and infer actual original normalized Q with exact physical reduction. No derived geometry/lift outcome is an input. -/
private def originalActualClosedPointPhysicalPositiveTest018
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (hRK : Function.Surjective (algebraMap R K))
    {v : ℕ} (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree
      (originalNormalizedHypersurfacePolynomial312 r (originalActualClosedPointChartChoice018 R r hr K P)) (originalActualClosedPointCoefficientIndex018 R r hr K P hRK))
    (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree
      (originalNormalizedHypersurfacePolynomial312 r (originalActualClosedPointChartChoice018 R r hr K P)) (originalActualClosedPointCoefficientIndex018 R r hr K P hRK))) [q.IsPrime]
    (hq : RingHom.ker (originalActualClosedPointCoefficientMap018 R r hr K P hRK).toRingHom = q)
    (N : ℕ) (hN : 0 < N) :=
  originalActualClosedPointPhysicalPresentation018 R r hr K P hK0 hRK f hf q hq N hN

/-- The ORIGINAL closed point and smooth cubic construct ALL canonical
thick-to-thin physical normalized test lifts. Chosen chart/index/field map,
whole field-family identity, HZ and upstairs membership are all derived.
No desired physical lift, chart-membership or classifier diagram is assumed. -/
lemma originalClosedPoint_canonicalTests_physicalLift317
    [IsNoetherianRing R] [Smooth (hypersurfaceToBase r hr)]
    (hK0 : r.map (algebraMap R K) ≠ 0)
    (hRK : Function.Surjective (algebraMap R K)) :
    ∃ (j : Fin 4) (i : MonomialCoefficientChartIndex300 3 pointDegree)
      (k : MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i →ₐ[R] K) (hk : Function.Surjective k),
      (originalCoefficientTestProjectiveFamily317 R pointDegree r hr j pointPositive i k).val =
        ((hypersurface (r.map (algebraMap R K)) (hr.map (algebraMap R K))).fromSpecResidueField P.val).ker ∧
      ∀ (v : ℕ) (f : MvPolynomial (Fin v) R →ₐ[R] MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)
        (hf : Function.Surjective f) (q : Ideal (MonomialPolynomialContainmentCoefficientAlgebra310 R 3 pointDegree (originalNormalizedHypersurfacePolynomial312 r j) i)) [q.IsPrime]
        (hq : RingHom.ker k.toRingHom = q) (N : ℕ) (hN : 0 < N),
    ∃ Q : FiniteFlatHilbertPoint195
        (Spec.map (CommRingCat.ofHom (R := (Localization.AtPrime (q.comap f.toRingHom) ⧸ obstructionThickIdeal316 (maximalIdeal (Localization.AtPrime (q.comap f.toRingHom))) (RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))) N))
          (S := OriginalNormalizedHypersurfaceAlgebra312 (r.map (algebraMap R (Localization.AtPrime (q.comap f.toRingHom) ⧸ obstructionThickIdeal316 (maximalIdeal (Localization.AtPrime (q.comap f.toRingHom))) (RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))) N))) j)
          (algebraMap (Localization.AtPrime (q.comap f.toRingHom) ⧸ obstructionThickIdeal316 (maximalIdeal (Localization.AtPrime (q.comap f.toRingHom))) (RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))) N) (OriginalNormalizedHypersurfaceAlgebra312
            (r.map (algebraMap R (Localization.AtPrime (q.comap f.toRingHom) ⧸ obstructionThickIdeal316 (maximalIdeal (Localization.AtPrime (q.comap f.toRingHom))) (RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))) N))) j)))) pointDegree,
      originalNormalizedAffinePointReduction317 R (Ideal.Quotient.factorₐ R (obstructionThickIdeal_le_thin316 (maximalIdeal (Localization.AtPrime (q.comap f.toRingHom))) (RingHom.ker (AlgHom.toRingHom (localSurjectivePresentationMap316 f q))) N)) r hr j pointDegree Q =
        originalCoefficientTestPhysicalFamily317 R pointDegree r hr j pointPositive i
          (localPolynomialArtinianChartTest316 f hf q N) := by
  refine ⟨(originalActualClosedPointChartChoice018 R r hr K P), (originalActualClosedPointCoefficientIndex018 R r hr K P hRK), (originalActualClosedPointCoefficientMap018 R r hr K P hRK),
    (originalActualClosedPointCoefficientSurjective018 R r hr K P hRK), (originalActualClosedPointCoefficientWholeIdeal018 R r hr K P hRK), ?_⟩
  intro v f hf q hprime hq N hN
  exact originalActualClosedPointPhysicalPositiveTest018 R r hr K P hK0 hRK f hf q hq N hN

end OriginalCanonicalPoint
end PfaffianDescent
end
