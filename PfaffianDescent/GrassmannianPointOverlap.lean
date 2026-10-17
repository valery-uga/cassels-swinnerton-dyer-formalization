import PfaffianDescent.GrassmannianChartEvaluation

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [CommRing K] {A : Type u} [CommRing A] [Algebra K A] {m n : ℕ}

lemma grassmannianChartEvaluation_injective :
    Function.Injective (grassmannianChartEvaluation K : Matrix (Fin n) (Fin m) A → _) := by
  intro T U h
  let cT : Fin n × Fin m → A := fun ij => T ij.1 ij.2
  let cU : Fin n × Fin m → A := fun ij => U ij.1 ij.2
  change Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) cT).toRingHom) =
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := K) cU).toRingHom) at h
  have he : (MvPolynomial.aeval (R := K) cT).toRingHom = (MvPolynomial.aeval (R := K) cU).toRingHom :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  funext i j
  have hx : MvPolynomial.aeval (R := K) cT (MvPolynomial.X (i, j)) =
      MvPolynomial.aeval (R := K) cU (MvPolynomial.X (i, j)) := RingHom.congr_fun he (MvPolynomial.X (i, j))
  simpa only [MvPolynomial.aeval_X] using hx

lemma grassmannianChartEvaluation_factor_bijective (σ : Equiv.Perm (Fin m ⊕ Fin n))
    (T : Matrix (Fin n) (Fin m) A) (a : Spec (.of A) ⟶ grassmannianOverlapScheme K σ)
    (ha : a ≫ grassmannianOverlapι K σ = grassmannianChartEvaluation K T) :
    Function.Bijective (graphTransitionFirst (graphCoordinatePermutation A σ) (Matrix.toLin' T)) := by
  let φ := Spec.preimage a
  have hp : Spec.map (CommRingCat.ofHom (algebraMap (GrassmannianChartRing K m n)
        (GrassmannianOverlapRing K σ)) ≫ φ) = grassmannianChartEvaluation K T := by
    exact (Spec.map_comp _ φ).trans
      ((congrArg (fun f => f ≫ grassmannianOverlapι K σ) (Spec.map_preimage a)).trans ha)
  have he := Spec.map_injective hp
  have hd := congrArg (fun f : CommRingCat.of (GrassmannianChartRing K m n) ⟶ CommRingCat.of A =>
    f.hom (grassmannianOverlapPolynomial K σ)) he
  have hu : IsUnit (φ.hom (algebraMap (GrassmannianChartRing K m n) (GrassmannianOverlapRing K σ)
      (grassmannianOverlapPolynomial K σ))) :=
    (IsLocalization.Away.algebraMap_isUnit (grassmannianOverlapPolynomial K σ)).map φ.hom
  apply (graphOverlapDeterminant_isUnit_iff _ _).mp
  rw [← grassmannianOverlapPolynomial_eval K σ T]
  exact hd ▸ hu

lemma grassmannianChartOverlap_isPullback (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    IsPullback (grassmannianOverlapι K (grassmannianChartChange i j))
      (grassmannianOverlapOtherι K (grassmannianChartChange i j))
      (grassmannianChartι K i) (grassmannianChartι K j) := by
  have h : IsPullback (grassmannianAtlasι K i j)
      (grassmannianAtlasTransition K i j ≫ grassmannianAtlasι K j i)
      (grassmannianChartι K i) (grassmannianChartι K j) :=
    IsPullback.of_isLimit (grassmannianChart_intersection K i j)
  rw [grassmannianAtlasTransition_ι] at h
  exact h

/-- Equality of two scheme-valued matrix points is precisely the actual graph transition on their overlap. -/
theorem grassmannianChartEvaluation_eq_transition (i j : Equiv.Perm (Fin m ⊕ Fin n))
    (T U : Matrix (Fin n) (Fin m) A)
    (he : grassmannianChartEvaluation K T ≫ grassmannianChartι K i =
      grassmannianChartEvaluation K U ≫ grassmannianChartι K j) :
    ∃ h : Function.Bijective (graphTransitionFirst
      (graphCoordinatePermutation A (grassmannianChartChange i j)) (Matrix.toLin' T)),
      graphTransitionMatrix (grassmannianChartChange i j) T h = U := by
  let H := grassmannianChartOverlap_isPullback K i j
  let a := H.lift (grassmannianChartEvaluation K T) (grassmannianChartEvaluation K U) he
  have ha : a ≫ grassmannianOverlapι K (grassmannianChartChange i j) = grassmannianChartEvaluation K T :=
    H.lift_fst _ _ he
  have hb : a ≫ grassmannianOverlapOtherι K (grassmannianChartChange i j) = grassmannianChartEvaluation K U :=
    H.lift_snd _ _ he
  have h := grassmannianChartEvaluation_factor_bijective K _ T a ha
  obtain ⟨b, hb₁, hb₂⟩ := grassmannianChartEvaluation_overlap K (grassmannianChartChange i j) T h
  have hab : a = b := (cancel_mono (grassmannianOverlapι K (grassmannianChartChange i j))).mp (ha.trans hb₁.symm)
  refine ⟨h, grassmannianChartEvaluation_injective K ?_⟩
  exact hb₂.symm.trans ((congrArg (fun a => a ≫ grassmannianOverlapOtherι K _) hab).symm.trans hb)

end
end PfaffianDescent
