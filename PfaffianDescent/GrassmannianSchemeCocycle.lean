import PfaffianDescent.GrassmannianSchemeCoordinates

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K] {m n : ℕ}

lemma grassmannianOverlapOtherι_toBase (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianOverlapOtherι K σ ≫ grassmannianChartToBase K m n =
      grassmannianOverlapι K σ ≫ grassmannianChartToBase K m n := by
  let φ : GrassmannianChartRing K m n →ₐ[K] GrassmannianOverlapRing K σ :=
    MvPolynomial.aeval (fun ij : Fin n × Fin m => grassmannianOverlapTransitionMatrix K σ ij.1 ij.2)
  have hφ : φ.toRingHom.comp MvPolynomial.C =
      (algebraMap (GrassmannianChartRing K m n) (GrassmannianOverlapRing K σ)).comp MvPolynomial.C := by
    apply RingHom.ext
    intro k
    change φ (algebraMap K (GrassmannianChartRing K m n) k) = _
    rw [φ.commutes]
    exact (IsScalarTower.algebraMap_apply K (GrassmannianChartRing K m n)
      (GrassmannianOverlapRing K σ) k).symm
  rw [grassmannianOverlapOtherι_eq]
  change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) =
    Spec.map (CommRingCat.ofHom (algebraMap (GrassmannianChartRing K m n) (GrassmannianOverlapRing K σ))) ≫
      Spec.map (CommRingCat.ofHom MvPolynomial.C)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hφ]

/-- Scheme-theoretic compatibility on a triple overlap. The intermediate
factorization is an actual scheme morphism, and both equalities hold on all
test schemes, without reducedness or affineness assumptions. -/
theorem grassmannian_scheme_transition_cocycle {X : Scheme.{u}}
    (σ τ : Equiv.Perm (Fin m ⊕ Fin n))
    (g : X ⟶ grassmannianOverlapScheme K σ)
    (h : X ⟶ grassmannianOverlapScheme K (τ.trans σ))
    (hgh : g ≫ grassmannianOverlapι K σ = h ≫ grassmannianOverlapι K (τ.trans σ)) :
    ∃ c : X ⟶ grassmannianOverlapScheme K τ,
      c ≫ grassmannianOverlapι K τ = g ≫ grassmannianOverlapOtherι K σ ∧
      c ≫ grassmannianOverlapOtherι K τ = h ≫ grassmannianOverlapOtherι K (τ.trans σ) := by
  let f := g ≫ grassmannianOverlapι K σ
  let q := g ≫ grassmannianOverlapOtherι K σ
  have hs := (grassmannianChart_factor_iff K f σ).mp ⟨g, rfl⟩
  have hst := (grassmannianChart_factor_iff K f (τ.trans σ)).mp ⟨h, hgh.symm⟩
  have hq : grassmannianChartMatrix K q = graphTransitionMatrix σ (grassmannianChartMatrix K f) hs :=
    grassmannianChartMatrix_transition K σ g hs
  have ht' := (graphTransitionMatrix_overlap_after σ τ (grassmannianChartMatrix K f) hs).mpr hst
  have ht : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation Γ(X, ⊤) τ)
      (Matrix.toLin' (grassmannianChartMatrix K q))) := by
    rw [hq]
    exact ht'
  let c := grassmannianChartLift K q τ ht
  have hc : c ≫ grassmannianOverlapι K τ = q := grassmannianChartLift_fac K q τ ht
  refine ⟨c, hc, grassmannianChart_morphism_ext K _ _ ?_ ?_⟩
  · calc
      (c ≫ grassmannianOverlapOtherι K τ) ≫ grassmannianChartToBase K m n =
          (c ≫ grassmannianOverlapι K τ) ≫ grassmannianChartToBase K m n := by
            simp only [Category.assoc, grassmannianOverlapOtherι_toBase]
      _ = (g ≫ grassmannianOverlapOtherι K σ) ≫ grassmannianChartToBase K m n := by rw [hc]
      _ = (g ≫ grassmannianOverlapι K σ) ≫ grassmannianChartToBase K m n := by
            simp only [Category.assoc, grassmannianOverlapOtherι_toBase]
      _ = (h ≫ grassmannianOverlapι K (τ.trans σ)) ≫ grassmannianChartToBase K m n := by rw [hgh]
      _ = (h ≫ grassmannianOverlapOtherι K (τ.trans σ)) ≫ grassmannianChartToBase K m n := by
            simp only [Category.assoc, grassmannianOverlapOtherι_toBase]
  · have hc' := (grassmannianChart_factor_iff K (c ≫ grassmannianOverlapι K τ) τ).mp ⟨c, rfl⟩
    have hh' := (grassmannianChart_factor_iff K (h ≫ grassmannianOverlapι K (τ.trans σ))
      (τ.trans σ)).mp ⟨h, rfl⟩
    calc
      grassmannianChartMatrix K (c ≫ grassmannianOverlapOtherι K τ) =
          graphTransitionMatrix τ (grassmannianChartMatrix K (c ≫ grassmannianOverlapι K τ)) hc' :=
            grassmannianChartMatrix_transition K τ c hc'
      _ = graphTransitionMatrix τ (grassmannianChartMatrix K q) ht :=
            graphTransitionMatrix_congr τ (congrArg (grassmannianChartMatrix K) hc) hc' ht
      _ = graphTransitionMatrix τ (graphTransitionMatrix σ (grassmannianChartMatrix K f) hs) ht' :=
            graphTransitionMatrix_congr τ hq ht ht'
      _ = graphTransitionMatrix (τ.trans σ) (grassmannianChartMatrix K f) hst :=
            graphTransitionMatrix_cocycle σ τ (grassmannianChartMatrix K f) hs ht' hst
      _ = graphTransitionMatrix (τ.trans σ)
          (grassmannianChartMatrix K (h ≫ grassmannianOverlapι K (τ.trans σ))) hh' :=
            graphTransitionMatrix_congr (τ.trans σ) (congrArg (grassmannianChartMatrix K) hgh) hst hh'
      _ = grassmannianChartMatrix K (h ≫ grassmannianOverlapOtherι K (τ.trans σ)) :=
            (grassmannianChartMatrix_transition K (τ.trans σ) h hh').symm

lemma grassmannian_scheme_transition_cocycle_of_eq {X : Scheme.{u}}
    (σ τ υ : Equiv.Perm (Fin m ⊕ Fin n)) (he : τ.trans σ = υ)
    (g : X ⟶ grassmannianOverlapScheme K σ) (h : X ⟶ grassmannianOverlapScheme K υ)
    (hgh : g ≫ grassmannianOverlapι K σ = h ≫ grassmannianOverlapι K υ) :
    ∃ c : X ⟶ grassmannianOverlapScheme K τ,
      c ≫ grassmannianOverlapι K τ = g ≫ grassmannianOverlapOtherι K σ ∧
      c ≫ grassmannianOverlapOtherι K τ = h ≫ grassmannianOverlapOtherι K υ := by
  subst υ
  exact grassmannian_scheme_transition_cocycle K σ τ g h hgh

end
end PfaffianDescent
