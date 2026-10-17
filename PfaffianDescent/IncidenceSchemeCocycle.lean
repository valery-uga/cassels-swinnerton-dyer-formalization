import PfaffianDescent.IncidenceSchemeCoordinates

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u
section
variable (K : Type u) [CommRing K]

lemma incidenceOverlapOtherι_toBase (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceOverlapOtherι K σ ≫ incidenceGraphToBase K = incidenceOverlapι K σ ≫ incidenceGraphToBase K := by
  let φ : IncidenceGraphRing K →ₐ[K] IncidenceOverlapRing K σ :=
    MvPolynomial.aeval (incidenceGraphPointCoordinates (IncidenceOverlapRing K σ) (incidenceOverlapTransitionPoint K σ))
  have hφ : φ.toRingHom.comp MvPolynomial.C =
      (algebraMap (IncidenceGraphRing K) (IncidenceOverlapRing K σ)).comp MvPolynomial.C := by
    apply RingHom.ext
    intro k
    change φ (algebraMap K (IncidenceGraphRing K) k) = _
    rw [φ.commutes]
    exact (IsScalarTower.algebraMap_apply K (IncidenceGraphRing K) (IncidenceOverlapRing K σ) k).symm
  rw [incidenceOverlapOtherι_eq]
  change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) =
    Spec.map (CommRingCat.ofHom (algebraMap (IncidenceGraphRing K) (IncidenceOverlapRing K σ))) ≫
      Spec.map (CommRingCat.ofHom MvPolynomial.C)
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hφ]

/-- The actual incidence scheme transitions satisfy the triple-overlap condition
on every test scheme, including its nilpotent structure. -/
theorem incidence_scheme_transition_cocycle {X : Scheme.{u}}
    (σ τ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (g : X ⟶ incidenceOverlapScheme K σ)
    (h : X ⟶ incidenceOverlapScheme K (τ.trans σ))
    (hgh : g ≫ incidenceOverlapι K σ = h ≫ incidenceOverlapι K (τ.trans σ)) :
    ∃ c : X ⟶ incidenceOverlapScheme K τ,
      c ≫ incidenceOverlapι K τ = g ≫ incidenceOverlapOtherι K σ ∧
      c ≫ incidenceOverlapOtherι K τ = h ≫ incidenceOverlapOtherι K (τ.trans σ) := by
  let f := g ≫ incidenceOverlapι K σ
  let q := g ≫ incidenceOverlapOtherι K σ
  have hs := (incidenceChart_factor_iff K f σ).mp ⟨g, rfl⟩
  have hst := (incidenceChart_factor_iff K f (τ.trans σ)).mp ⟨h, hgh.symm⟩
  have hq : incidenceChartPoint K q =
      incidencePointTransition (graphCoordinatePermutation Γ(X, ⊤) σ) (incidenceChartPoint K f) hs :=
    incidenceChartPoint_transition K σ g hs
  have ht' := (incidencePointTransition_overlap_after σ τ (incidenceChartPoint K f) hs).mpr hst
  have ht : Function.Bijective (graphTransitionFirst (graphCoordinatePermutation Γ(X, ⊤) τ)
      (incidenceChartPoint K q).1) := by
    rw [hq]
    exact ht'
  let c := incidenceChartLift K q τ ht
  have hc : c ≫ incidenceOverlapι K τ = q := incidenceChartLift_fac K q τ ht
  refine ⟨c, hc, incidenceChart_morphism_ext K _ _ ?_ ?_⟩
  · calc
      (c ≫ incidenceOverlapOtherι K τ) ≫ incidenceGraphToBase K =
          (c ≫ incidenceOverlapι K τ) ≫ incidenceGraphToBase K := by
            simp only [Category.assoc, incidenceOverlapOtherι_toBase]
      _ = (g ≫ incidenceOverlapOtherι K σ) ≫ incidenceGraphToBase K := by rw [hc]
      _ = (g ≫ incidenceOverlapι K σ) ≫ incidenceGraphToBase K := by
            simp only [Category.assoc, incidenceOverlapOtherι_toBase]
      _ = (h ≫ incidenceOverlapι K (τ.trans σ)) ≫ incidenceGraphToBase K := by rw [hgh]
      _ = (h ≫ incidenceOverlapOtherι K (τ.trans σ)) ≫ incidenceGraphToBase K := by
            simp only [Category.assoc, incidenceOverlapOtherι_toBase]
  · have hc' := (incidenceChart_factor_iff K (c ≫ incidenceOverlapι K τ) τ).mp ⟨c, rfl⟩
    have hh' := (incidenceChart_factor_iff K (h ≫ incidenceOverlapι K (τ.trans σ)) (τ.trans σ)).mp ⟨h, rfl⟩
    calc
      incidenceChartPoint K (c ≫ incidenceOverlapOtherι K τ) =
          incidencePointTransition (graphCoordinatePermutation Γ(X, ⊤) τ)
            (incidenceChartPoint K (c ≫ incidenceOverlapι K τ)) hc' :=
              incidenceChartPoint_transition K τ c hc'
      _ = incidencePointTransition (graphCoordinatePermutation Γ(X, ⊤) τ) (incidenceChartPoint K q) ht :=
            incidencePointTransition_congr _ (congrArg (incidenceChartPoint K) hc) hc' ht
      _ = incidencePointTransition (graphCoordinatePermutation Γ(X, ⊤) τ)
            (incidencePointTransition (graphCoordinatePermutation Γ(X, ⊤) σ) (incidenceChartPoint K f) hs) ht' :=
              incidencePointTransition_congr _ hq ht ht'
      _ = incidencePointTransition (graphCoordinatePermutation Γ(X, ⊤) (τ.trans σ)) (incidenceChartPoint K f) hst :=
            incidencePointTransition_cocycle_permutation σ τ (incidenceChartPoint K f) hs ht' hst
      _ = incidencePointTransition (graphCoordinatePermutation Γ(X, ⊤) (τ.trans σ))
            (incidenceChartPoint K (h ≫ incidenceOverlapι K (τ.trans σ))) hh' :=
              incidencePointTransition_congr _ (congrArg (incidenceChartPoint K) hgh) hst hh'
      _ = incidenceChartPoint K (h ≫ incidenceOverlapOtherι K (τ.trans σ)) :=
            (incidenceChartPoint_transition K (τ.trans σ) h hh').symm

lemma incidence_scheme_transition_cocycle_of_eq {X : Scheme.{u}}
    (σ τ υ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (he : τ.trans σ = υ)
    (g : X ⟶ incidenceOverlapScheme K σ) (h : X ⟶ incidenceOverlapScheme K υ)
    (hgh : g ≫ incidenceOverlapι K σ = h ≫ incidenceOverlapι K υ) :
    ∃ c : X ⟶ incidenceOverlapScheme K τ,
      c ≫ incidenceOverlapι K τ = g ≫ incidenceOverlapOtherι K σ ∧
      c ≫ incidenceOverlapOtherι K τ = h ≫ incidenceOverlapOtherι K υ := by
  subst υ
  exact incidence_scheme_transition_cocycle K σ τ g h hgh

end
end PfaffianDescent
